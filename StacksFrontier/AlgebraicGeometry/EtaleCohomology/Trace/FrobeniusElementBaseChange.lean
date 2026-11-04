module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FrobeniusElementDegree
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurvePointInertiaGeometry
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.SpecializationMap

/-!
# Frobenius elements under a morphism of schemes

Let `g : X' ⟶ X` be a morphism of connected schemes, `y'` a closed point of `X'` with finite
residue field whose image `y = g(y')` is closed in `X`, and `e = [κ(y') : κ(y)]`. Then the image
under `π₁(X', x̄') → π₁(X, g(x̄'))` of the geometric Frobenius element at `y'` is conjugate to the
`e`-th power of the geometric Frobenius element at `y`.

## Main definitions

* `AlgebraicGeometry.GeometricPoint.fiberFunctorIsoOfSourceIso`: the isomorphism of geometric
  fibre functors given by an isomorphism of the sources of two geometric points.

## Main results

* `AlgebraicGeometry.etaleFundamentalGroupMulEquiv_fiberFunctorIsoOfSourceIso_sourceAutElement`.
* `AlgebraicGeometry.exists_etaleFundamentalGroupMap_geometricFrobeniusFamily_eq_conj_pow`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Frobenius

universe u

namespace AlgebraicGeometry

/-! ### Isomorphisms of the sources of geometric points -/

section SourceIso

variable {S : Scheme.{u}}

/-- **The isomorphism of geometric fibre functors given by an isomorphism of sources**: for
`γ : Spec Ω₁ ≅ Spec Ω₂` over `S`, precomposition with `γ` identifies the fibre at `z₂` with the
fibre at `z₁`. -/
def GeometricPoint.fiberFunctorIsoOfSourceIso (z₁ z₂ : GeometricPoint S)
    (γ : z₁.source ≅ z₂.source) (hγ : γ.hom ≫ z₂.hom = z₁.hom) :
    finiteEtaleFiberFunctor z₂ ≅ finiteEtaleFiberFunctor z₁ :=
  NatIso.ofComponents (fun V => Equiv.toIso
    { toFun := fun q => ⟨γ.hom ≫ q.1, by rw [Category.assoc, q.2, hγ]⟩
      invFun := fun q => ⟨γ.inv ≫ q.1, by rw [Category.assoc, q.2, ← hγ, Iso.inv_hom_id_assoc]⟩
      left_inv := fun q => Subtype.ext (by simp)
      right_inv := fun q => Subtype.ext (by simp) })
    (fun {V W} f => by
      ext q
      exact Subtype.ext (Category.assoc _ _ _).symm)

/-- **Transport of the element of an automorphism of the source along an isomorphism of
sources**: if `α₁ ≫ γ = γ ≫ α₂`, the element of `α₂` at `z₂` is carried to the element of `α₁` at
`z₁`. -/
theorem etaleFundamentalGroupMulEquiv_fiberFunctorIsoOfSourceIso_sourceAutElement
    [ConnectedSpace S] (z₁ z₂ : GeometricPoint S) (γ : z₁.source ≅ z₂.source)
    (hγ : γ.hom ≫ z₂.hom = z₁.hom) (α₁ : z₁.source ≅ z₁.source) (α₂ : z₂.source ≅ z₂.source)
    (h₁ : α₁.hom ≫ z₁.hom = z₁.hom) (h₂ : α₂.hom ≫ z₂.hom = z₂.hom)
    (hc : α₁.hom ≫ γ.hom = γ.hom ≫ α₂.hom) :
    etaleFundamentalGroupMulEquiv (GeometricPoint.fiberFunctorIsoOfSourceIso z₁ z₂ γ hγ)
        (z₂.sourceAutElement α₂ h₂) = z₁.sourceAutElement α₁ h₁ := by
  refine Iso.ext (NatTrans.ext (funext fun V => ?_))
  ext q
  refine Subtype.ext ?_
  show γ.hom ≫ α₂.hom ≫ γ.inv ≫ q.1 = α₁.hom ≫ q.1
  rw [← Category.assoc, ← hc, Category.assoc, Iso.hom_inv_id_assoc]

/-- Powers of an automorphism fixing a morphism `f` also fix `f`. -/
private theorem aut_pow_hom_comp_eq {A B : Scheme.{u}} (α : Aut A) (f : A ⟶ B)
    (hα : α.hom ≫ f = f) (n : ℕ) : (α ^ n).hom ≫ f = f := by
  induction n with
  | zero => exact Category.id_comp _
  | succ n ih =>
      rw [pow_succ, Aut.Aut_mul_def]
      show (α.hom ≫ (α ^ n).hom) ≫ f = f
      rw [Category.assoc, ih, hα]

/-- **The elements of the powers of an automorphism of the source are the powers.** -/
theorem GeometricPoint.sourceAutElement_pow [ConnectedSpace S] (z : GeometricPoint S)
    (α : Aut z.source) (hα : α.hom ≫ z.hom = z.hom) (n : ℕ)
    (hαn : (α ^ n).hom ≫ z.hom = z.hom) :
    z.sourceAutElement (α ^ n) hαn = z.sourceAutElement α hα ^ n := by
  induction n with
  | zero =>
      refine Iso.ext (NatTrans.ext (funext fun V => ?_))
      ext q
      exact Subtype.ext (Category.id_comp _)
  | succ n ih =>
      have hn := aut_pow_hom_comp_eq α z.hom hα n
      calc z.sourceAutElement (α ^ (n + 1)) hαn
          = z.sourceAutElement (α ≪≫ α ^ n) _ :=
            Stacks.EtaleCohomology.GeometricPoint.sourceAutElement_congr z
              (by rw [pow_succ, Aut.Aut_mul_def]) hαn
        _ = z.sourceAutElement α hα * z.sourceAutElement (α ^ n) hn :=
            Stacks.EtaleCohomology.GeometricPoint.sourceAutElement_trans z α (α ^ n) hα hn
        _ = z.sourceAutElement α hα ^ (n + 1) := by rw [ih hn, ← pow_succ']

/-- The automorphism `Spec σ` of `Spec Ω` given by a ring automorphism `σ` of `Ω`. -/
def specRingEquivIso {Ω : Type u} [Field Ω] (σ : Ω ≃+* Ω) : Aut (Spec (.of Ω)) where
  hom := Spec.map (CommRingCat.ofHom σ.toRingHom)
  inv := Spec.map (CommRingCat.ofHom σ.symm.toRingHom)
  hom_inv_id := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    convert Spec.map_id (CommRingCat.of Ω)
    ext x
    simp
  inv_hom_id := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    convert Spec.map_id (CommRingCat.of Ω)
    ext x
    simp

/-- The powers of `Spec σ` are the spectra of the powers of `σ`. -/
theorem specRingEquivIso_pow_hom {Ω : Type u} [Field Ω] (σ : Ω ≃+* Ω) (n : ℕ) :
    (specRingEquivIso σ ^ n).hom =
      Spec.map (CommRingCat.ofHom ((σ : RingAut Ω) ^ n).toRingHom) := by
  induction n with
  | zero =>
      show 𝟙 _ = _
      rw [pow_zero]
      exact (Spec.map_id _).symm
  | succ n ih =>
      rw [pow_succ, Aut.Aut_mul_def]
      show Spec.map _ ≫ (specRingEquivIso σ ^ n).hom = _
      rw [ih, ← Spec.map_comp, ← CommRingCat.ofHom_comp, pow_succ']
      rfl

end SourceIso

/-! ### The arithmetic Frobenius element as the element of an automorphism of the source -/

section LocalElement

variable {X : Scheme.{u}} [ConnectedSpace X] (base : GeometricPoint X) (y : closedPoints X)
  [Finite (X.residueField y.1)]

omit [ConnectedSpace X] in
/-- The arithmetic Frobenius of `κ(y)^alg` fixes the geometric point above `y`. -/
theorem specRingEquivIso_residueGeometricFrobenius_symm_comp :
    (specRingEquivIso (residueGeometricFrobenius X y.1).symm.toRingEquiv).hom ≫
      (geometricPointAt X y.1).hom = (geometricPointAt X y.1).hom := by
  show Spec.map _ ≫ Spec.map _ ≫ _ = Spec.map _ ≫ _
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 3
  exact RingHom.ext fun a => (residueGeometricFrobenius X y.1).symm.commutes a

/-- **The arithmetic Frobenius element at `y` is the element of the arithmetic Frobenius of the
source** of the geometric point above `y`. -/
theorem localElement_frobeniusDataOfPath_eq_sourceAutElement
    (t : finiteEtaleFiberFunctor (geometricPointAt X y.1) ≅ finiteEtaleFiberFunctor base) :
    (Stacks.EtaleCohomology.frobeniusDataOfPath base y t).localElement =
      (geometricPointAt X y.1).sourceAutElement
        (specRingEquivIso (residueGeometricFrobenius X y.1).symm.toRingEquiv)
        (specRingEquivIso_residueGeometricFrobenius_symm_comp y) := by
  refine Iso.ext (NatTrans.ext (funext fun V => ?_))
  ext q
  refine Subtype.ext ?_
  exact Stacks.EtaleCohomology.localElement_app_coe base y t V q

end LocalElement

/-! ### Frobenius elements under a morphism -/

section BaseChange

variable {X X' : Scheme.{u}} [ConnectedSpace X] [ConnectedSpace X'] (g : X' ⟶ X)
  (x' : GeometricPoint X') (y' : closedPoints X') (hy : g.base y'.1 ∈ closedPoints X)
  [Finite (X'.residueField y'.1)] [Finite (X.residueField (g.base y'.1))]

/-- The powers of a ring automorphism raising to the power `N` raise to the powers of `N`. -/
theorem ringAut_pow_apply_eq_pow {Ω : Type*} [Field Ω] (σ : RingAut Ω) {N : ℕ}
    (hσ : ∀ a, σ a = a ^ N) (n : ℕ) (a : Ω) : (σ ^ n) a = a ^ N ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', RingAut.mul_apply, ih, hσ, ← pow_mul, ← pow_succ]

/-- The residue degree `[κ(y') : κ(g(y'))]`. -/
def residueFieldMapDegree : ℕ :=
  letI := (g.residueFieldMap y'.1).hom.toAlgebra
  Module.finrank (X.residueField (g.base y'.1)) (X'.residueField y'.1)

omit [ConnectedSpace X] [ConnectedSpace X'] [Finite (X.residueField (g.base y'.1))] in
/-- The residue degree `[κ(y') : κ(g(y'))]` is positive. -/
theorem residueFieldMapDegree_ne_zero : residueFieldMapDegree g y' ≠ 0 := by
  let := (g.residueFieldMap y'.1).hom.toAlgebra
  have : Module.Finite (X.residueField (g.base y'.1)) (X'.residueField y'.1) :=
    Module.Finite.of_finite
  exact (Module.finrank_pos (R := X.residueField (g.base y'.1))
    (M := X'.residueField y'.1)).ne'

/-- **A Frobenius element at `y'` maps to a conjugate of the `[κ(y') : κ(y)]`-th power of a
Frobenius element at `y = g(y')`.** -/
theorem exists_etaleFundamentalGroupMap_element_eq_conj_pow
    (t' : finiteEtaleFiberFunctor (geometricPointAt X' y'.1) ≅ finiteEtaleFiberFunctor x')
    (t : finiteEtaleFiberFunctor (geometricPointAt X (g.base y'.1)) ≅
      finiteEtaleFiberFunctor (x'.map g)) :
    ∃ h : EtaleFundamentalGroup X (x'.map g),
      etaleFundamentalGroupMap g x' (Stacks.EtaleCohomology.frobeniusDataOfPath x' y' t').element =
        h * (Stacks.EtaleCohomology.frobeniusDataOfPath (x'.map g) ⟨g.base y'.1, hy⟩ t).element ^
          residueFieldMapDegree g y' * h⁻¹ := by
  let κ := X.residueField (g.base y'.1)
  let κ' := X'.residueField y'.1
  let : Algebra κ κ' := (g.residueFieldMap y'.1).hom.toAlgebra
  have : Module.Finite κ κ' := Module.Finite.of_finite
  have : Algebra.IsAlgebraic κ κ' := Algebra.IsAlgebraic.of_finite κ κ'
  let Ω := AlgebraicClosure κ
  let Ω' := AlgebraicClosure κ'
  let τ : Ω' ≃ₐ[κ] Ω := IsAlgClosure.equiv κ Ω' Ω
  let γ : Spec (.of Ω) ≅ Spec (.of Ω') :=
    { hom := Spec.map (CommRingCat.ofHom τ.toRingHom)
      inv := Spec.map (CommRingCat.ofHom τ.symm.toRingHom)
      hom_inv_id := by
        rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
        convert Spec.map_id (CommRingCat.of Ω)
        ext a
        simp
      inv_hom_id := by
        rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
        convert Spec.map_id (CommRingCat.of Ω')
        ext a
        simp }
  let z₁ := geometricPointAt X (g.base y'.1)
  let z₂ := (geometricPointAt X' y'.1).map g
  have hring : CommRingCat.ofHom (algebraMap κ Ω) = g.residueFieldMap y'.1 ≫
      CommRingCat.ofHom (algebraMap κ' Ω') ≫ CommRingCat.ofHom τ.toRingHom := by
    refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
    show algebraMap κ Ω a = τ (algebraMap κ' Ω' (algebraMap κ κ' a))
    rw [← IsScalarTower.algebraMap_apply, AlgEquiv.commutes]
  have hγ : γ.hom ≫ z₂.hom = z₁.hom := by
    have h1 : z₂.hom = Spec.map (CommRingCat.ofHom (algebraMap κ' Ω')) ≫
        Spec.map (g.residueFieldMap y'.1) ≫ X.fromSpecResidueField (g.base y'.1) := by
      show (Spec.map _ ≫ X'.fromSpecResidueField y'.1) ≫ g = _
      rw [Category.assoc, Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
    rw [h1]
    show Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ _ =
      Spec.map (CommRingCat.ofHom (algebraMap κ Ω)) ≫ X.fromSpecResidueField (g.base y'.1)
    refine Eq.trans ?_ (congrArg (fun φ => Spec.map φ ≫ X.fromSpecResidueField (g.base y'.1))
      hring.symm)
    simp only [Spec.map_comp, Category.assoc]
    exact ((congrArg (· ≫ _) (Spec.map_comp _ _)).trans (Category.assoc _ _ _)).symm
  let σ₁ := (residueGeometricFrobenius X (g.base y'.1)).symm.toRingEquiv
  let σ' := (residueGeometricFrobenius X' y'.1).symm.toRingEquiv
  set e := residueFieldMapDegree g y'
  have hcard : Nat.card κ' = Nat.card κ ^ e := by
    let : Fintype κ := Fintype.ofFinite _
    let : Fintype κ' := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact Module.card_eq_pow_finrank
  have hσ₁ : ∀ a, (σ₁ : RingAut Ω) a = a ^ Nat.card κ := fun a =>
    residueGeometricFrobenius_symm_apply X (g.base y'.1) a
  have hc : ((specRingEquivIso σ₁) ^ e).hom ≫ γ.hom = γ.hom ≫ (specRingEquivIso σ').hom := by
    rw [specRingEquivIso_pow_hom]
    show Spec.map (CommRingCat.ofHom ((σ₁ : RingAut Ω) ^ e).toRingHom) ≫
        Spec.map (CommRingCat.ofHom τ.toRingHom) =
      Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ Spec.map (CommRingCat.ofHom σ'.toRingHom)
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    refine RingHom.ext fun a => ?_
    show ((σ₁ : RingAut Ω) ^ e) (τ a) = τ (σ' a)
    rw [ringAut_pow_apply_eq_pow σ₁ hσ₁, ← hcard]
    show _ = τ ((residueGeometricFrobenius X' y'.1).symm a)
    rw [residueGeometricFrobenius_symm_apply, map_pow]
  have h₁ := specRingEquivIso_residueGeometricFrobenius_symm_comp (X := X) ⟨g.base y'.1, hy⟩
  have h₁e := aut_pow_hom_comp_eq (specRingEquivIso σ₁) z₁.hom h₁ e
  have h' := specRingEquivIso_residueGeometricFrobenius_symm_comp (X := X') y'
  have h₂ : (specRingEquivIso σ').hom ≫ z₂.hom = z₂.hom := by
    show _ ≫ (geometricPointAt X' y'.1).hom ≫ g = (geometricPointAt X' y'.1).hom ≫ g
    rw [← Category.assoc, h']
  let s := GeometricPoint.fiberFunctorIsoOfSourceIso z₁ z₂ γ hγ
  let T := fiberFunctorTransportIso g t'
  let L := (Stacks.EtaleCohomology.frobeniusDataOfPath (x'.map g) ⟨g.base y'.1, hy⟩ t).localElement
  have hL : L = z₁.sourceAutElement (specRingEquivIso σ₁) h₁ :=
    localElement_frobeniusDataOfPath_eq_sourceAutElement (x'.map g) ⟨g.base y'.1, hy⟩ t
  have hs :
      etaleFundamentalGroupMulEquiv s (z₂.sourceAutElement (specRingEquivIso σ') h₂) = L ^ e := by
    rw [etaleFundamentalGroupMulEquiv_fiberFunctorIsoOfSourceIso_sourceAutElement z₁ z₂ γ hγ
      ((specRingEquivIso σ₁) ^ e) (specRingEquivIso σ') h₁e h₂ hc,
      GeometricPoint.sourceAutElement_pow z₁ (specRingEquivIso σ₁) h₁ e h₁e]
    exact congrArg (· ^ e) hL.symm
  have hs' : z₂.sourceAutElement (specRingEquivIso σ') h₂ =
      etaleFundamentalGroupMulEquiv s.symm (L ^ e) := by
    rw [← hs, etaleFundamentalGroupMulEquiv_symm_apply_apply]
  have hmap : etaleFundamentalGroupMap g (geometricPointAt X' y'.1)
      (Stacks.EtaleCohomology.frobeniusDataOfPath x' y' t').localElement =
        z₂.sourceAutElement (specRingEquivIso σ') h₂ := by
    rw [localElement_frobeniusDataOfPath_eq_sourceAutElement x' y' t']
    exact etaleFundamentalGroupMap_sourceAutElement g _ _ _
  let hh : EtaleFundamentalGroup X (x'.map g) := t.symm ≪≫ s.symm ≪≫ T
  have hpath : s.symm ≪≫ T = t ≪≫ hh := by
    show _ = t ≪≫ t.symm ≪≫ s.symm ≪≫ T
    rw [Iso.self_symm_id_assoc]
  refine ⟨hh, ?_⟩
  have hel := FrobeniusData.element_path_trans
    (Stacks.EtaleCohomology.frobeniusDataOfPath (x'.map g) ⟨g.base y'.1, hy⟩ t) hh
  show etaleFundamentalGroupMap g x' (etaleFundamentalGroupMulEquiv t' _) = _
  calc etaleFundamentalGroupMap g x' (etaleFundamentalGroupMulEquiv t'
        (Stacks.EtaleCohomology.frobeniusDataOfPath x' y' t').localElement)
      = etaleFundamentalGroupMulEquiv T (etaleFundamentalGroupMap g (geometricPointAt X' y'.1)
          (Stacks.EtaleCohomology.frobeniusDataOfPath x' y' t').localElement) :=
        (etaleFundamentalGroupMulEquiv_transportIso g t' _).symm
    _ = etaleFundamentalGroupMulEquiv T (etaleFundamentalGroupMulEquiv s.symm (L ^ e)) := by
        rw [hmap, hs']
    _ = etaleFundamentalGroupMulEquiv (s.symm ≪≫ T) (L ^ e) :=
        (etaleFundamentalGroupMulEquiv_trans _ _ _).symm
    _ = etaleFundamentalGroupMulEquiv (t ≪≫ hh) L ^ e := by
        rw [hpath]
        exact _root_.map_pow (etaleFundamentalGroupMulEquiv (t ≪≫ hh)) L e
    _ = hh * (Stacks.EtaleCohomology.frobeniusDataOfPath (x'.map g) ⟨g.base y'.1, hy⟩ t).element ^
          e * hh⁻¹ :=
        (congrArg (· ^ e) hel).trans conj_pow

omit [Finite (X'.residueField y'.1)] [Finite (X.residueField (g.base y'.1))] in
/-- **The geometric Frobenius element at `y'` maps to a conjugate of the `[κ(y') : κ(y)]`-th power
of the geometric Frobenius element at `y = g(y')`**, for `X` and `X'` locally of finite type over
finite fields. -/
theorem exists_etaleFundamentalGroupMap_geometricFrobeniusFamily_eq_conj_pow {k k' : Type u}
    [Field k] [Finite k] [Field k'] [Finite k'] (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (f' : X' ⟶ Spec (.of k')) [LocallyOfFiniteType f'] :
    haveI := Stacks.EtaleCohomology.finite_residueField f' y'.1 y'.2
    haveI := Stacks.EtaleCohomology.finite_residueField f (g.base y'.1) hy
    ∃ h : EtaleFundamentalGroup X (x'.map g),
      etaleFundamentalGroupMap g x' (Stacks.EtaleCohomology.geometricFrobeniusFamily f' x' y') =
        h * Stacks.EtaleCohomology.geometricFrobeniusFamily f (x'.map g) ⟨g.base y'.1, hy⟩ ^
          residueFieldMapDegree g y' * h⁻¹ := by
  have := Stacks.EtaleCohomology.finite_residueField f' y'.1 y'.2
  have := Stacks.EtaleCohomology.finite_residueField f (g.base y'.1) hy
  obtain ⟨h, hh⟩ := exists_etaleFundamentalGroupMap_element_eq_conj_pow g x' y' hy
    (nonempty_finiteEtaleFiberFunctorIso X' (geometricPointAt X' y'.1) x').some
    (nonempty_finiteEtaleFiberFunctorIso X (geometricPointAt X (g.base y'.1)) (x'.map g)).some
  refine ⟨h, ?_⟩
  unfold Stacks.EtaleCohomology.geometricFrobeniusFamily
  rw [map_inv, hh]
  simp only [mul_inv_rev, inv_inv, inv_pow, mul_assoc]

end BaseChange

end AlgebraicGeometry

end
