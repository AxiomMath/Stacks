module

public import Mathlib.AlgebraicGeometry.Fiber
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Variety.Tangent.Defs
public import StacksFrontier.AlgebraicGeometry.Variety.Tangent.Functorial

/-!
# The tangent space of a fibre

Let `f : X ⟶ S` be a morphism of schemes and let `x` be a point of `X`. The relative tangent
space of `X` over `S` at `x` is the tangent space of the scheme-theoretic fibre `X_{f(x)}` at
the point of that fibre corresponding to `x`.

## Main definitions

* `AlgebraicGeometry.dualNumberCongr`: the isomorphism of dual-number rings induced by an
  isomorphism of coefficient rings.
* `AlgebraicGeometry.TangentSpaceFiberEquiv`: the semilinear identification of the relative
  tangent space with the tangent space of the fibre, together with its characterizations.

## Main results

* `AlgebraicGeometry.tangentSpaceEquivFiber`: the relative tangent space at `x` is the tangent
  space of the fibre at the corresponding point.

## Implementation notes

The residue field of `f.asFiber x` is canonically isomorphic, rather than definitionally equal,
to the residue field of `x`. Consequently the equality of the source is recorded as an additive
equivalence which is semilinear for that residue-field isomorphism. The equivalence is pinned
down by composition with the inclusion of the fibre, and the residue-field isomorphism by the
canonical residue-field point of the fibre; both characterizations are fields of
`AlgebraicGeometry.TangentSpaceFiberEquiv`, so the identification is specified rather than
merely asserted to exist.

## References

* [Stacks Project, Tag 0BEA](https://stacks.math.columbia.edu/tag/0BEA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

section DualNumbers

variable {R K L : Type*} [CommRing R] [CommRing K] [CommRing L]

/-- An isomorphism of rings induces an isomorphism of their dual-number rings. -/
def dualNumberCongr (e : R ≃+* K) : DualNumber R ≃+* DualNumber K where
  toFun z := (e z.1, e z.2)
  invFun z := (e.symm z.1, e.symm z.2)
  left_inv z := by
    rcases z with ⟨a, b⟩
    change (e.symm (e a), e.symm (e b)) = (a, b)
    simp
  right_inv z := by
    rcases z with ⟨a, b⟩
    change (e (e.symm a), e (e.symm b)) = (a, b)
    simp
  map_add' x y := by
    rcases x with ⟨a, b⟩
    rcases y with ⟨c, d⟩
    change (e (a + c), e (b + d)) = (e a + e c, e b + e d)
    simp
  map_mul' x y := by
    rcases x with ⟨a, b⟩
    rcases y with ⟨c, d⟩
    change (e (a * c), e (a * d + b * c)) =
      (e a * e c, e a * e d + e b * e c)
    simp

/-- The first component of `dualNumberCongr e z` is `e` applied to the first component of `z`. -/
@[simp]
lemma dualNumberCongr_fst (e : R ≃+* K) (z : DualNumber R) :
    TrivSqZeroExt.fst (dualNumberCongr e z) = e (TrivSqZeroExt.fst z) := rfl

/-- The second component of `dualNumberCongr e z` is `e` applied to the second component of
`z`. -/
@[simp]
lemma dualNumberCongr_snd (e : R ≃+* K) (z : DualNumber R) :
    TrivSqZeroExt.snd (dualNumberCongr e z) = e (TrivSqZeroExt.snd z) := rfl

/-- The inverse of `dualNumberCongr e` is `dualNumberCongr e.symm`. -/
lemma dualNumberCongr_symm (e : R ≃+* K) :
    (dualNumberCongr e).symm = dualNumberCongr e.symm := rfl

/-- `dualNumberCongr` sends a composite of ring isomorphisms to the composite of the induced
isomorphisms. -/
lemma dualNumberCongr_trans (e : R ≃+* K) (e' : K ≃+* L) :
    dualNumberCongr (e.trans e') = (dualNumberCongr e).trans (dualNumberCongr e') := rfl

end DualNumbers

section DualNumbersSpec

variable {R K : Type u} [CommRing R] [CommRing K]

/-- The dual-number isomorphism induced by an identification is inverse to the one induced by
the inverse identification. -/
lemma ofHom_dualNumberCongr_comp_symm (e : R ≃+* K) :
    CommRingCat.ofHom (dualNumberCongr e).toRingHom ≫
        CommRingCat.ofHom (dualNumberCongr e).symm.toRingHom = 𝟙 _ :=
  CommRingCat.hom_ext (RingHom.ext fun w => (dualNumberCongr e).symm_apply_apply w)

/-- The dual-number isomorphism induced by the inverse of an identification is inverse to the one
induced by the identification. -/
lemma ofHom_dualNumberCongr_symm_comp (e : R ≃+* K) :
    CommRingCat.ofHom (dualNumberCongr e).symm.toRingHom ≫
        CommRingCat.ofHom (dualNumberCongr e).toRingHom = 𝟙 _ :=
  CommRingCat.hom_ext (RingHom.ext fun w => (dualNumberCongr e).apply_symm_apply w)

/-- On spectra, the two dual-number isomorphisms attached to an identification compose to the
identity. -/
lemma specMap_dualNumberCongr_symm_comp (e : R ≃+* K) :
    Spec.map (CommRingCat.ofHom (dualNumberCongr e).symm.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (dualNumberCongr e).toRingHom) = 𝟙 _ := by
  rw [← Spec.map_comp, ofHom_dualNumberCongr_comp_symm, Spec.map_id]

/-- The companion of `AlgebraicGeometry.specMap_dualNumberCongr_symm_comp` in the other
order. -/
lemma specMap_dualNumberCongr_comp_symm (e : R ≃+* K) :
    Spec.map (CommRingCat.ofHom (dualNumberCongr e).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (dualNumberCongr e).symm.toRingHom) = 𝟙 _ := by
  rw [← Spec.map_comp, ofHom_dualNumberCongr_symm_comp, Spec.map_id]

/-- Precomposition with the spectrum of a dual-number isomorphism is injective. -/
private lemma cancel_specMap_dualNumberCongr (e : R ≃+* K) {Z : Scheme.{u}}
    {g g' : Spec (.of (DualNumber R)) ⟶ Z}
    (h : Spec.map (CommRingCat.ofHom (dualNumberCongr e).toRingHom) ≫ g =
      Spec.map (CommRingCat.ofHom (dualNumberCongr e).toRingHom) ≫ g') : g = g' :=
  haveI : IsIso (Spec.map (CommRingCat.ofHom (dualNumberCongr e).toRingHom)) :=
    ⟨⟨_, specMap_dualNumberCongr_comp_symm e, specMap_dualNumberCongr_symm_comp e⟩⟩
  (cancel_epi _).1 h

end DualNumbersSpec

/-- The canonical semilinear identification between the relative tangent space at `x` and the
tangent space of the fibre through `x` at the corresponding point. -/
structure TangentSpaceFiberEquiv {X S : Scheme.{u}} (f : X ⟶ S) (x : X) where
  /-- The canonical identification of the residue fields of `f.asFiber x` and `x`. -/
  residueFieldEquiv :
    (f.fiber (f x)).residueField (f.asFiber x) ≃+* X.residueField x
  /-- The residue-field identification is the one induced by the canonical residue-field point
  of the fibre. -/
  residueFieldEquiv_spec :
    Spec.map (CommRingCat.ofHom residueFieldEquiv.toRingHom) ≫
        (f.fiber (f x)).fromSpecResidueField (f.asFiber x) =
      f.asFiberHom x
  /-- The additive equivalence between the two tangent spaces. -/
  toAddEquiv :
    DottedTangentArrow f x ≃+
      DottedTangentArrow (f.fiberToSpecResidueField (f x)) (f.asFiber x)
  /-- The equivalence is induced by the inclusion of the fibre into `X`. -/
  toAddEquiv_fiberι (v : DottedTangentArrow f x) :
    Spec.map (CommRingCat.ofHom (dualNumberCongr residueFieldEquiv).toRingHom) ≫
        (toAddEquiv v).val ≫ f.fiberι (f x) = v.val
  /-- The equivalence is semilinear for the canonical residue-field isomorphism. -/
  toAddEquiv_smul (r : X.residueField x) (v : DottedTangentArrow f x) :
    toAddEquiv (r • v) = residueFieldEquiv.symm r • toAddEquiv v

/-- Transporting an additive equivalence along an equality of its source index. -/
lemma eqCast_addEquiv_apply {I : Type u} {A : I → Type u} {B : Type u}
    [∀ i, AddCommGroup (A i)] [AddCommGroup B]
    {i j : I} (h : i = j) (g : A i ≃+ B) (a : A j) :
    (congrArg (fun k => A k ≃+ B) h ▸ g) a =
      g (Eq.mp (congrArg A h.symm) a) := by
  cases h
  rfl

/-- Transporting a tangent arrow along an equality of base points changes its underlying
morphism only by the induced isomorphism of dual-number rings. -/
lemma dottedArrow_eqCast_val {X S : Scheme.{u}} (f : X ⟶ S)
    {x y : X} (h : y = x) (v : DottedTangentArrow f x) :
    Spec.map (CommRingCat.ofHom
      (dualNumberCongr (X.residueFieldCongr h).commRingCatIsoToRingEquiv).toRingHom) ≫
        (Eq.mp (congrArg (DottedTangentArrow f) h.symm) v).val = v.val := by
  cases h
  rw [Scheme.residueFieldCongr_refl]
  have hid : dualNumberCongr ((Iso.refl (X.residueField x)).commRingCatIsoToRingEquiv) =
      RingEquiv.refl (DualNumber (X.residueField x)) :=
    RingEquiv.ext fun _ => rfl
  rw [hid]
  simp

variable {X S : Scheme.{u}} (f : X ⟶ S) (x : X)

/-- The inclusion of the fibre through `x` induces an isomorphism on residue fields at `x`. -/
lemma isIso_residueFieldMap_fiberι :
    IsIso ((f.fiberι (f x)).residueFieldMap (f.asFiber x)) := by
  set j := f.fiberι (f x) with hj
  set z := f.asFiber x with hz
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨(j.residueFieldMap z).hom.injective, ?_⟩
  have heq := Scheme.residue_residueFieldMap j z
  have hsurj : Function.Surjective (j.stalkMap z ≫
      (f.fiber (f x)).residue z).hom := by
    rw [CommRingCat.hom_comp]
    exact ((f.fiber (f x)).residue_surjective z).comp (j.stalkMap_surjective z)
  rw [← heq] at hsurj
  rw [CommRingCat.hom_comp, RingHom.coe_comp] at hsurj
  exact Function.Surjective.of_comp hsurj

/-- The residue field of the fibre at `f.asFiber x`, identified with the residue field of `X`
at the image of that point under the inclusion of the fibre. -/
noncomputable def fiberResidueFieldIso :
    (f.fiber (f x)).residueField (f.asFiber x) ≃+*
      X.residueField (f.fiberι (f x) (f.asFiber x)) :=
  letI := isIso_residueFieldMap_fiberι f x
  (asIso ((f.fiberι (f x)).residueFieldMap (f.asFiber x))).symm.commRingCatIsoToRingEquiv

/-- The residue field of the fibre at `f.asFiber x`, identified with the residue field of `X`
at `x`. -/
noncomputable def fiberResidueFieldEquiv :
    (f.fiber (f x)).residueField (f.asFiber x) ≃+* X.residueField x :=
  (fiberResidueFieldIso f x).trans
    (X.residueFieldCongr (f.fiberι_asFiber x)).commRingCatIsoToRingEquiv

/-- Composing the residue-field map of the fibre inclusion with `fiberResidueFieldEquiv` gives the
canonical identification of the residue fields of `X` at `f.fiberι (f x) (f.asFiber x)` and `x`. -/
private lemma residueFieldMap_fiberι_comp_fiberResidueFieldEquiv :
    (f.fiberι (f x)).residueFieldMap (f.asFiber x) ≫
        CommRingCat.ofHom (fiberResidueFieldEquiv f x).toRingHom =
      (X.residueFieldCongr (f.fiberι_asFiber x)).hom := by
  have := isIso_residueFieldMap_fiberι f x
  apply CommRingCat.hom_ext
  have hinv : ((inv ((f.fiberι (f x)).residueFieldMap (f.asFiber x))).hom).comp
      ((f.fiberι (f x)).residueFieldMap (f.asFiber x)).hom = RingHom.id _ := by
    apply RingHom.ext
    intro a
    simp
  change ((X.residueFieldCongr (f.fiberι_asFiber x)).hom.hom.comp
    ((inv ((f.fiberι (f x)).residueFieldMap (f.asFiber x))).hom)).comp
    ((f.fiberι (f x)).residueFieldMap (f.asFiber x)).hom =
      (X.residueFieldCongr (f.fiberι_asFiber x)).hom.hom
  rw [RingHom.comp_assoc, hinv]
  simp

/-- The residue-field identification of `AlgebraicGeometry.fiberResidueFieldEquiv` is the one
induced by the canonical residue-field point of the fibre. -/
lemma fiberResidueFieldEquiv_spec :
    Spec.map (CommRingCat.ofHom (fiberResidueFieldEquiv f x).toRingHom) ≫
        (f.fiber (f x)).fromSpecResidueField (f.asFiber x) =
      f.asFiberHom x := by
  let z := f.asFiber x
  let j := f.fiberι (f x)
  have : IsIso (j.residueFieldMap z) := isIso_residueFieldMap_fiberι f x
  have hjz : j z = x := f.fiberι_asFiber x
  let e : (f.fiber (f x)).residueField z ≃+* X.residueField x :=
    fiberResidueFieldEquiv f x
  show Spec.map (CommRingCat.ofHom e.toRingHom) ≫
      (f.fiber (f x)).fromSpecResidueField z = f.asFiberHom x
  apply (cancel_mono j).1
  rw [Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
  have hCongr := X.residueFieldCongr_fromSpecResidueField hjz
  have hRing := residueFieldMap_fiberι_comp_fiberResidueFieldEquiv f x
  have hSpec := congrArg Spec.map hRing
  calc
    _ = Spec.map (CommRingCat.ofHom e.toRingHom) ≫
        Spec.map (j.residueFieldMap z) ≫ X.fromSpecResidueField (j z) := by rfl
    _ = Spec.map ((X.residueFieldCongr hjz).hom) ≫
        X.fromSpecResidueField (j z) := by
          rw [← Spec.map_comp_assoc]
          exact congrArg (fun k => k ≫ X.fromSpecResidueField (j z)) hSpec
    _ = X.fromSpecResidueField x := hCongr
    _ = f.asFiberHom x ≫ j := (Scheme.Hom.asFiberHom_fiberι f x).symm

/-- Tangent arrows of the fibre at `f.asFiber x` are the same data as tangent arrows of the
composite of the fibre inclusion with `f`: a derivation annihilates the image of the residue
field of `f x` exactly when it annihilates the image of the local ring of `S` at `f x`. -/
noncomputable def fiberTangentBridge :
    DottedTangentArrow (f.fiberToSpecResidueField (f x)) (f.asFiber x) ≃+
      DottedTangentArrow (f.fiberι (f x) ≫ f) (f.asFiber x) := by
  let z := f.asFiber x
  let j := f.fiberι (f x)
  have : IsIso (j.residueFieldMap z) := isIso_residueFieldMap_fiberι f x
  have hjz : j z = x := f.fiberι_asFiber x
  let e : (f.fiber (f x)).residueField z ≃+* X.residueField x :=
    fiberResidueFieldEquiv f x
  let p := f.fiberToSpecResidueField (f x)
  let q := S.fromSpecResidueField (f x)
  have hcomp : j ≫ f = p ≫ q := f.fiber_fac (f x)
  letI : Module ((f.fiber (f x)).presheaf.stalk z)
      ((f.fiber (f x)).residueField z) :=
    Module.compHom _ ((f.fiber (f x)).residue z).hom
  letI : SMulCommClass ((f.fiber (f x)).residueField z)
      ((f.fiber (f x)).presheaf.stalk z) ((f.fiber (f x)).residueField z) := ⟨by
    intro r a v
    change r * (((f.fiber (f x)).residue z a) * v) =
      ((f.fiber (f x)).residue z a) * (r * v)
    ring⟩
  have hcond (D : Derivation ℤ ((f.fiber (f x)).presheaf.stalk z)
      ((f.fiber (f x)).residueField z)) :
      D ∈ tangentDerivations p z ↔
        D ∈ tangentDerivations (j ≫ f) z := by
    rw [hcomp]
    change (∀ b : (Spec (S.residueField (f x))).presheaf.stalk (p z),
        D (p.stalkMap z b) = 0) ↔
      (∀ a : S.presheaf.stalk ((p ≫ q) z),
        D ((p ≫ q).stalkMap z a) = 0)
    simp only [Scheme.Hom.stalkMap_comp]
    have hq := q.stalkMap_surjective (p z)
    constructor
    · intro h a
      have hb := h (q.stalkMap (p z) a)
      change D ((p.stalkMap z) (q.stalkMap (p z) a)) = 0 at hb
      exact hb
    · intro h b
      obtain ⟨a, ha⟩ := hq b
      subst b
      exact h a
  let dEquiv : tangentDerivations p z ≃ₗ[
      (f.fiber (f x)).residueField z]
      tangentDerivations (j ≫ f) z := {
    toFun := fun D => ⟨D.val, (hcond D.val).mp D.property⟩
    invFun := fun D => ⟨D.val, (hcond D.val).mpr D.property⟩
    left_inv := by intro D; apply Subtype.ext; rfl
    right_inv := by intro D; apply Subtype.ext; rfl
    map_add' := by intro D E; apply Subtype.ext; rfl
    map_smul' := by intro r D; apply Subtype.ext; rfl }
  let compBridge : DottedTangentArrow p z ≃+
      DottedTangentArrow (j ≫ f) z :=
    (dottedDerivationEquiv p z).addEquiv.trans
      (dEquiv.toAddEquiv.trans
        (dottedDerivationEquiv (j ≫ f) z).addEquiv.symm)
  exact compBridge

/-- The bridge of `AlgebraicGeometry.fiberTangentBridge` leaves the underlying morphism of a
tangent arrow unchanged. -/
lemma fiberTangentBridge_val
    (w : DottedTangentArrow (f.fiberToSpecResidueField (f x)) (f.asFiber x)) :
    (fiberTangentBridge f x w).val = w.val :=
  congrArg Subtype.val
    (derivationToDotted_dottedToDerivation (f.fiberToSpecResidueField (f x)) (f.asFiber x) w)

/-- The tangent map along the inclusion of the fibre sends a tangent arrow to its composite with
the inclusion, pulled back along the dual-number isomorphism of the residue fields. -/
private lemma tangentMap_fiberι_val (θ : DottedTangentArrow (f.fiberι (f x) ≫ f) (f.asFiber x)) :
    letI := isIso_residueFieldMap_fiberι f x
    (tangentMap (f.fiberι (f x)) (f.fiberι (f x) ≫ f) f rfl (f.asFiber x) θ).val =
      Spec.map (CommRingCat.ofHom (dualNumberCongr (fiberResidueFieldIso f x)).toRingHom) ≫
        θ.val ≫ f.fiberι (f x) :=
  letI := isIso_residueFieldMap_fiberι f x
  tangentMap_apply (f.fiberι (f x)) (f.fiberι (f x) ≫ f) f rfl (f.asFiber x) θ _
    (fun _ => rfl) fun _ => rfl

/-- The tangent map along the inclusion of the fibre is injective. -/
lemma injective_tangentMap_fiberι :
    letI := isIso_residueFieldMap_fiberι f x
    Function.Injective
      (tangentMap (f.fiberι (f x)) (f.fiberι (f x) ≫ f) f rfl (f.asFiber x)) := by
  intro a b hab
  apply Subtype.ext
  have hval := congrArg Subtype.val hab
  rw [tangentMap_fiberι_val, tangentMap_fiberι_val] at hval
  exact cancel_specMap_dualNumberCongr _ ((cancel_mono _).1 (by simpa using hval))

/-- The tangent map along the inclusion of the fibre is surjective: a tangent arrow of `X`
over `S` at `x` factors through the fibre by the universal property of the pullback. -/
lemma surjective_tangentMap_fiberι :
    letI := isIso_residueFieldMap_fiberι f x
    Function.Surjective
      (tangentMap (f.fiberι (f x)) (f.fiberι (f x) ≫ f) f rfl (f.asFiber x)) := by
  let z := f.asFiber x
  let j := f.fiberι (f x)
  have : IsIso (j.residueFieldMap z) := isIso_residueFieldMap_fiberι f x
  have hjz : j z = x := f.fiberι_asFiber x
  let e : (f.fiber (f x)).residueField z ≃+* X.residueField x :=
    fiberResidueFieldEquiv f x
  let p := f.fiberToSpecResidueField (f x)
  let q := S.fromSpecResidueField (f x)
  have hcomp : j ≫ f = p ≫ q := f.fiber_fac (f x)
  let T := tangentMap j (j ≫ f) f rfl z
  show Function.Surjective T
  intro θ
  let e0 : (f.fiber (f x)).residueField z ≃+* X.residueField (j z) :=
    ((asIso (j.residueFieldMap z)).symm).commRingCatIsoToRingEquiv
  let α := dualNumberCongr e0
  let θ' := Spec.map (CommRingCat.ofHom α.symm.toRingHom) ≫ θ.val
  let b := Spec.map (CommRingCat.ofHom
      (((algebraMap ((f.fiber (f x)).residueField z)
        (DualNumber ((f.fiber (f x)).residueField z))).comp
        (e.symm.toRingHom.comp (f.residueFieldMap x).hom))))
  let c := S.residueFieldCongr (congrArg f hjz)
  have hRing := residueFieldMap_fiberι_comp_fiberResidueFieldEquiv f x
  have hR : (j ≫ f).residueFieldMap z ≫ CommRingCat.ofHom e.toRingHom =
      c.hom ≫ f.residueFieldMap x := by
    rw [Scheme.residueFieldMap_comp]
    refine (Category.assoc _ _ _).trans ?_
    rw [hRing]
    exact Scheme.Hom.residueFieldMap_congr' (f := f) hjz
  have hRpt (s' : S.residueField ((j ≫ f) z)) :
      ((j ≫ f).residueFieldMap z).hom s' =
        e.symm ((f.residueFieldMap x).hom ((c.hom).hom s')) := by
    have ha : e (((j ≫ f).residueFieldMap z).hom s') =
        (f.residueFieldMap x).hom ((c.hom).hom s') :=
      DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hR) s'
    rw [← ha, e.symm_apply_apply]
  have hq : q = Spec.map c.hom ≫
      S.fromSpecResidueField (f (j z)) := by
    dsimp [q, c]
    exact (S.residueFieldCongr_fromSpecResidueField
      (congrArg f hjz)).symm
  have hidx : (j ≫ f) z = f (j z) := by simp
  have hbasePoint : dualNumberBasePoint (j ≫ f) z = b ≫ q := by
    let aF := CommRingCat.ofHom
      (algebraMap ((f.fiber (f x)).residueField z)
        (DualNumber ((f.fiber (f x)).residueField z)))
    let bF := CommRingCat.ofHom
      (((algebraMap ((f.fiber (f x)).residueField z)
        (DualNumber ((f.fiber (f x)).residueField z))).comp
        (e.symm.toRingHom.comp (f.residueFieldMap x).hom)))
    have hBR : Spec.map aF ≫ Spec.map ((j ≫ f).residueFieldMap z) =
        Spec.map bF ≫ Spec.map c.hom := by
      have hRingBase :
          (j ≫ f).residueFieldMap z ≫ aF = c.hom ≫ bF := by
        refine CommRingCat.hom_ext (RingHom.ext fun s' => ?_)
        show aF.hom (((j ≫ f).residueFieldMap z).hom s') = bF.hom ((c.hom).hom s')
        rw [hRpt s']
        rfl
      exact (Spec.map_comp _ _).symm.trans
        ((congrArg Spec.map hRingBase).trans (Spec.map_comp _ _))
    calc
      _ = Spec.map aF ≫ Spec.map ((j ≫ f).residueFieldMap z) ≫
            S.fromSpecResidueField (f (j z)) := by
          dsimp [dualNumberBasePoint]
      _ = (Spec.map bF ≫ Spec.map c.hom) ≫
            S.fromSpecResidueField (f (j z)) :=
          (Category.assoc _ _ _).symm.trans
            (congrArg (fun k => k ≫ S.fromSpecResidueField (f (j z))) hBR)
      _ = b ≫ q := by
          rw [hq]
          rfl
  have he0 : e0.symm.toRingHom = (j.residueFieldMap z).hom := by
    apply RingHom.ext
    intro a
    rfl
  have hfromSpec :
      Spec.map (CommRingCat.ofHom e0.symm.toRingHom) ≫
          X.fromSpecResidueField (j z) =
        (f.fiber (f x)).fromSpecResidueField z ≫ j := by
    rw [he0]
    exact Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField j z
  have hcompat0 : θ' ≫ f = dualNumberBasePoint (j ≫ f) z := by
    have hfSpec :
        Spec.map (f.residueFieldMap (j z)) ≫
            S.fromSpecResidueField (f (j z)) =
          X.fromSpecResidueField (j z) ≫ f := by
      exact Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField f (j z)
    have hcoeff :
        CommRingCat.ofHom
            (algebraMap (X.residueField (j z))
              (DualNumber (X.residueField (j z)))) ≫
            CommRingCat.ofHom α.symm.toRingHom =
          CommRingCat.ofHom e0.symm.toRingHom ≫
            CommRingCat.ofHom (algebraMap
              ((f.fiber (f x)).residueField z)
              (DualNumber ((f.fiber (f x)).residueField z))) := by
      apply CommRingCat.hom_ext
      ext a
      case h1 =>
        show e0.symm a = e0.symm a
        rfl
      case h2 =>
        show ((dualNumberCongr e0).symm (TrivSqZeroExt.inl a)).snd =
          (TrivSqZeroExt.inl (e0.symm a)).snd
        simp only [dualNumberCongr]
        show e0.symm (TrivSqZeroExt.snd (TrivSqZeroExt.inl a)) =
          (TrivSqZeroExt.inl (e0.symm a)).snd
        rw [TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inl]
        exact map_zero e0.symm
    have hcoeffSpec :
        Spec.map (CommRingCat.ofHom α.symm.toRingHom) ≫
            Spec.map (CommRingCat.ofHom (algebraMap
              (X.residueField (j z))
              (DualNumber (X.residueField (j z))))) =
          Spec.map (CommRingCat.ofHom (algebraMap
            ((f.fiber (f x)).residueField z)
            (DualNumber ((f.fiber (f x)).residueField z)))) ≫
            Spec.map (CommRingCat.ofHom e0.symm.toRingHom) := by
      rw [← Spec.map_comp, ← Spec.map_comp]
      exact congrArg Spec.map hcoeff
    have hbasef : dualNumberBasePoint f (j z) =
        Spec.map (CommRingCat.ofHom (algebraMap
          (X.residueField (j z))
          (DualNumber (X.residueField (j z))))) ≫
          X.fromSpecResidueField (j z) ≫ f := by
      dsimp [dualNumberBasePoint]
      simp
    have hbasejf : dualNumberBasePoint (j ≫ f) z =
        Spec.map (CommRingCat.ofHom (algebraMap
          ((f.fiber (f x)).residueField z)
          (DualNumber ((f.fiber (f x)).residueField z)))) ≫
          (f.fiber (f x)).fromSpecResidueField z ≫ j ≫ f := by
      dsimp [dualNumberBasePoint]
      simp [Category.assoc]
    calc
      θ' ≫ f = Spec.map (CommRingCat.ofHom α.symm.toRingHom) ≫
          (θ.val ≫ f) := by simp [θ', Category.assoc]
      _ = Spec.map (CommRingCat.ofHom α.symm.toRingHom) ≫
            dualNumberBasePoint f (j z) := by
          rw [θ.property.2]
      _ = Spec.map (CommRingCat.ofHom α.symm.toRingHom) ≫
            (Spec.map (CommRingCat.ofHom (algebraMap
              (X.residueField (j z))
              (DualNumber (X.residueField (j z))))) ≫
              X.fromSpecResidueField (j z) ≫ f) := by rw [hbasef]
      _ = Spec.map (CommRingCat.ofHom (algebraMap
            ((f.fiber (f x)).residueField z)
            (DualNumber ((f.fiber (f x)).residueField z)))) ≫
            (f.fiber (f x)).fromSpecResidueField z ≫ j ≫ f := by
          calc
            _ = ((Spec.map (CommRingCat.ofHom α.symm.toRingHom) ≫
                Spec.map (CommRingCat.ofHom (algebraMap
                  (X.residueField (j z))
                  (DualNumber (X.residueField (j z)))))) ≫
                X.fromSpecResidueField (j z)) ≫ f := by simp [Category.assoc]
            _ = ((Spec.map (CommRingCat.ofHom (algebraMap
                  ((f.fiber (f x)).residueField z)
                  (DualNumber ((f.fiber (f x)).residueField z)))) ≫
                Spec.map (CommRingCat.ofHom e0.symm.toRingHom)) ≫
                X.fromSpecResidueField (j z)) ≫ f := by
                  rw [hcoeffSpec]
            _ = (Spec.map (CommRingCat.ofHom (algebraMap
                  ((f.fiber (f x)).residueField z)
                  (DualNumber ((f.fiber (f x)).residueField z)))) ≫
                ((f.fiber (f x)).fromSpecResidueField z ≫ j)) ≫ f := by
                  simpa [Category.assoc] using congrArg
                    (fun k => (Spec.map (CommRingCat.ofHom (algebraMap
                      ((f.fiber (f x)).residueField z)
                      (DualNumber ((f.fiber (f x)).residueField z)))) ≫ k) ≫ f)
                    hfromSpec
            _ = _ := by simp [Category.assoc]
      _ = dualNumberBasePoint (j ≫ f) z := hbasejf.symm
  have hcompat : θ' ≫ f = b ≫ S.fromSpecResidueField (f x) := by
    calc
      θ' ≫ f = dualNumberBasePoint (j ≫ f) z := hcompat0
      _ = b ≫ q := hbasePoint
      _ = b ≫ S.fromSpecResidueField (f x) := rfl
  let ηval : Spec (.of (DualNumber ((f.fiber (f x)).residueField z))) ⟶
      f.fiber (f x) := by
    show _ ⟶ pullback f (S.fromSpecResidueField (f x))
    exact pullback.lift θ' b hcompat
  have hfst : ηval ≫ j = θ' := by
    show pullback.lift θ' b hcompat ≫ pullback.fst f
      (S.fromSpecResidueField (f x)) = θ'
    exact pullback.lift_fst θ' b hcompat
  have hsnd : ηval ≫ p = b := by
    show pullback.lift θ' b hcompat ≫ pullback.snd f
      (S.fromSpecResidueField (f x)) = b
    exact pullback.lift_snd θ' b hcompat
  have hclosed : dualNumberClosedPoint (f.fiber (f x)) z ≫ ηval =
      (f.fiber (f x)).fromSpecResidueField z := by
    have hclosedcomp :
        dualNumberClosedPoint (f.fiber (f x)) z ≫
            Spec.map (CommRingCat.ofHom α.symm.toRingHom) =
          Spec.map (CommRingCat.ofHom e0.symm.toRingHom) ≫
            dualNumberClosedPoint X (j z) := by
      dsimp [dualNumberClosedPoint]
      rw [← Spec.map_comp, ← Spec.map_comp]
      apply congrArg Spec.map
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro w
      rfl
    apply (cancel_mono j).mp
    rw [Category.assoc, hfst]
    show (dualNumberClosedPoint (f.fiber (f x)) z ≫
      Spec.map (CommRingCat.ofHom α.symm.toRingHom)) ≫ θ.val =
        (f.fiber (f x)).fromSpecResidueField z ≫ j
    rw [hclosedcomp, Category.assoc, θ.property.1,
      hfromSpec]
  have hbase : ηval ≫ (j ≫ f) =
      dualNumberBasePoint (j ≫ f) z := by
    calc
      ηval ≫ (j ≫ f) = ηval ≫ (p ≫ q) := by rw [hcomp]
      _ = (ηval ≫ p) ≫ q := by simp [Category.assoc]
      _ = b ≫ q := by rw [hsnd]
      _ = dualNumberBasePoint (j ≫ f) z := hbasePoint.symm
  let η : DottedTangentArrow (j ≫ f) z := ⟨ηval, hclosed, hbase⟩
  refine ⟨η, ?_⟩
  apply Subtype.ext
  show (T η).val = θ.val
  rw [tangentMap_fiberι_val]
  show Spec.map (CommRingCat.ofHom α.toRingHom) ≫ ηval ≫ j = θ.val
  have hαinv : Spec.map (CommRingCat.ofHom α.toRingHom) ≫
      Spec.map (CommRingCat.ofHom α.symm.toRingHom) = 𝟙 _ :=
    specMap_dualNumberCongr_comp_symm e0
  calc
    Spec.map (CommRingCat.ofHom α.toRingHom) ≫ ηval ≫ j =
        Spec.map (CommRingCat.ofHom α.toRingHom) ≫ θ' := by
      rw [hfst]
    _ = θ.val := by
      show (Spec.map (CommRingCat.ofHom α.toRingHom) ≫
        Spec.map (CommRingCat.ofHom α.symm.toRingHom)) ≫ θ.val = θ.val
      rw [hαinv, Category.id_comp]

/-- The relative tangent space at the image of `f.asFiber x` under the inclusion of the
fibre is the tangent space of the fibre at `f.asFiber x`. -/
noncomputable def fiberTangentCore :
    DottedTangentArrow f (f.fiberι (f x) (f.asFiber x)) ≃+
      DottedTangentArrow (f.fiberToSpecResidueField (f x)) (f.asFiber x) :=
  letI := isIso_residueFieldMap_fiberι f x
  (AddEquiv.ofBijective
      (tangentMap (f.fiberι (f x)) (f.fiberι (f x) ≫ f) f rfl
        (f.asFiber x)).toAddMonoidHom
      ⟨injective_tangentMap_fiberι f x, surjective_tangentMap_fiberι f x⟩).symm.trans
    (fiberTangentBridge f x).symm

/-- The relative tangent space at `x` is the tangent space of the fibre at the corresponding
point. -/
noncomputable def fiberTangentEquiv :
    DottedTangentArrow f x ≃+
      DottedTangentArrow (f.fiberToSpecResidueField (f x)) (f.asFiber x) :=
  congrArg (fun y => DottedTangentArrow f y ≃+
      DottedTangentArrow (f.fiberToSpecResidueField (f x)) (f.asFiber x))
    (f.fiberι_asFiber x) ▸ fiberTangentCore f x

/-- `AlgebraicGeometry.fiberTangentEquiv` is `AlgebraicGeometry.fiberTangentCore` read at
`x` rather than at the image of `f.asFiber x`. -/
lemma fiberTangentEquiv_apply (v : DottedTangentArrow f x) :
    fiberTangentEquiv f x v =
      fiberTangentCore f x
        (Eq.mp (congrArg (DottedTangentArrow f) (f.fiberι_asFiber x).symm) v) :=
  eqCast_addEquiv_apply (f.fiberι_asFiber x) (fiberTangentCore f x) v

/-- `AlgebraicGeometry.fiberTangentCore` is inverse to the tangent map along the inclusion of
the fibre. -/
lemma tangentMap_fiberTangentCore
    (v : DottedTangentArrow f (f.fiberι (f x) (f.asFiber x))) :
    letI := isIso_residueFieldMap_fiberι f x
    tangentMap (f.fiberι (f x)) (f.fiberι (f x) ≫ f) f rfl (f.asFiber x)
      (fiberTangentBridge f x (fiberTangentCore f x v)) = v := by
  have := isIso_residueFieldMap_fiberι f x
  let T := AddEquiv.ofBijective
    (tangentMap (f.fiberι (f x)) (f.fiberι (f x) ≫ f) f rfl
      (f.asFiber x)).toAddMonoidHom
    ⟨injective_tangentMap_fiberι f x, surjective_tangentMap_fiberι f x⟩
  show T (fiberTangentBridge f x ((fiberTangentBridge f x).symm (T.symm v))) = v
  rw [(fiberTangentBridge f x).apply_symm_apply, T.apply_symm_apply]

/-- The identification of `AlgebraicGeometry.fiberTangentEquiv` is the one induced by the
inclusion of the fibre into `X`. -/
lemma fiberTangentEquiv_fiberι (v : DottedTangentArrow f x) :
    Spec.map (CommRingCat.ofHom (dualNumberCongr (fiberResidueFieldEquiv f x)).toRingHom) ≫
        (fiberTangentEquiv f x v).val ≫ f.fiberι (f x) = v.val := by
  let z := f.asFiber x
  let j := f.fiberι (f x)
  have : IsIso (j.residueFieldMap z) := isIso_residueFieldMap_fiberι f x
  have hjz : j z = x := f.fiberι_asFiber x
  let e : (f.fiber (f x)).residueField z ≃+* X.residueField x :=
    fiberResidueFieldEquiv f x
  let T := tangentMap j (j ≫ f) f rfl z
  show Spec.map (CommRingCat.ofHom (dualNumberCongr e).toRingHom) ≫
      (fiberTangentEquiv f x v).val ≫ j = v.val
  let v' : DottedTangentArrow f (j z) :=
    Eq.mp (congrArg (DottedTangentArrow f) hjz.symm) v
  let w := fiberTangentEquiv f x v
  have hw : w = fiberTangentCore f x v' := fiberTangentEquiv_apply f x v
  have hT : T (fiberTangentBridge f x w) = v' := by
    rw [hw]
    exact tangentMap_fiberTangentCore f x v'
  let e0 := fiberResidueFieldIso f x
  let α := dualNumberCongr e0
  have hchar := tangentMap_fiberι_val f x (fiberTangentBridge f x w)
  have hv := congrArg Subtype.val hT
  rw [hchar, fiberTangentBridge_val f x w] at hv
  let γ := (X.residueFieldCongr hjz).commRingCatIsoToRingEquiv
  have he : e = e0.trans γ := by rfl
  have hdual : dualNumberCongr e = (dualNumberCongr e0).trans
      (dualNumberCongr γ) := by
    apply RingEquiv.ext
    intro u
    cases u with
    | mk a b => rfl
  have hSpec : Spec.map (CommRingCat.ofHom (dualNumberCongr e).toRingHom) =
      Spec.map (CommRingCat.ofHom (dualNumberCongr γ).toRingHom) ≫
        Spec.map (CommRingCat.ofHom α.toRingHom) := by
    rw [hdual, ← Spec.map_comp]
    rfl
  calc
    _ = (Spec.map (CommRingCat.ofHom (dualNumberCongr γ).toRingHom) ≫
        Spec.map (CommRingCat.ofHom α.toRingHom)) ≫ w.val ≫ j := by rw [hSpec]
    _ = Spec.map (CommRingCat.ofHom (dualNumberCongr γ).toRingHom) ≫
          (Spec.map (CommRingCat.ofHom α.toRingHom) ≫ w.val ≫ j) := by
            simp [Category.assoc]
    _ = Spec.map (CommRingCat.ofHom (dualNumberCongr γ).toRingHom) ≫ v'.val := by
            rw [hv]
    _ = v.val := dottedArrow_eqCast_val f hjz v

/-- The identification of `AlgebraicGeometry.fiberTangentEquiv` is semilinear for the
canonical residue-field isomorphism. -/
lemma fiberTangentEquiv_smul (r : X.residueField x) (v : DottedTangentArrow f x) :
    fiberTangentEquiv f x (r • v) =
      (fiberResidueFieldEquiv f x).symm r • fiberTangentEquiv f x v := by
  let z := f.asFiber x
  let j := f.fiberι (f x)
  let e : (f.fiber (f x)).residueField z ≃+* X.residueField x :=
    fiberResidueFieldEquiv f x
  let p := f.fiberToSpecResidueField (f x)
  apply Subtype.ext
  apply (cancel_mono j).1
  let σ := Spec.map (CommRingCat.ofHom (dualNumberCongr e).toRingHom)
  have hscale : σ ≫ scaleDualNumberMap
      ((f.fiber (f x)).residueField z) (e.symm r) =
      scaleDualNumberMap (X.residueField x) r ≫ σ := by
    show Spec.map (CommRingCat.ofHom (dualNumberCongr e).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (scaleDualNumber
          ((f.fiber (f x)).residueField z) (e.symm r)).toRingHom) =
      Spec.map (CommRingCat.ofHom (scaleDualNumber
          (X.residueField x) r).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (dualNumberCongr e).toRingHom)
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro w
    show dualNumberCongr e
        (scaleDualNumber
          ((f.fiber (f x)).residueField z) (e.symm r) w) =
      scaleDualNumber (X.residueField x) r (dualNumberCongr e w)
    apply TrivSqZeroExt.ext
    · show e (TrivSqZeroExt.fst (scaleDualNumber
          ((f.fiber (f x)).residueField z) (e.symm r) w)) =
        TrivSqZeroExt.fst (scaleDualNumber
          (X.residueField x) r (dualNumberCongr e w))
      rw [scaleDualNumber, TrivSqZeroExt.fst_map,
        scaleDualNumber, TrivSqZeroExt.fst_map]
      rfl
    · show e (TrivSqZeroExt.snd (scaleDualNumber
          ((f.fiber (f x)).residueField z) (e.symm r) w)) =
        TrivSqZeroExt.snd (scaleDualNumber
          (X.residueField x) r (dualNumberCongr e w))
      rw [scaleDualNumber, TrivSqZeroExt.snd_map,
        scaleDualNumber, TrivSqZeroExt.snd_map]
      show e (e.symm r * TrivSqZeroExt.snd w) =
        r * e (TrivSqZeroExt.snd w)
      calc
        e (e.symm r * TrivSqZeroExt.snd w) =
            e (e.symm r) * e (TrivSqZeroExt.snd w) := e.map_mul _ _
        _ = r * e (TrivSqZeroExt.snd w) := by rw [e.apply_symm_apply]
  have hsmul : (e.symm r • fiberTangentEquiv f x v).val =
      scaleDualNumberMap
        ((f.fiber (f x)).residueField z) (e.symm r) ≫ (fiberTangentEquiv f x v).val :=
    (dottedTangentArrowModule p z).smul_apply (e.symm r) (fiberTangentEquiv f x v)
  refine cancel_specMap_dualNumberCongr e ?_
  calc
    σ ≫ (fiberTangentEquiv f x (r • v)).val ≫ j = (r • v).val :=
      fiberTangentEquiv_fiberι f x (r • v)
    _ = scaleDualNumberMap (X.residueField x) r ≫ v.val :=
      (dottedTangentArrowModule f x).smul_apply r v
    _ = scaleDualNumberMap (X.residueField x) r ≫ σ ≫ (fiberTangentEquiv f x v).val ≫ j := by
      rw [fiberTangentEquiv_fiberι f x v]
    _ = σ ≫ scaleDualNumberMap ((f.fiber (f x)).residueField z) (e.symm r) ≫
          (fiberTangentEquiv f x v).val ≫ j := by
      rw [← Category.assoc, ← hscale, Category.assoc]
    _ = σ ≫ (e.symm r • fiberTangentEquiv f x v).val ≫ j := by rw [hsmul, Category.assoc]

/-- The tangent space of `X` over `S` at `x` is canonically identified with the tangent space of
the fibre `X_{f(x)}` at its corresponding point. -/
@[stacks 0BEA]
noncomputable def tangentSpaceEquivFiber : TangentSpaceFiberEquiv f x where
  residueFieldEquiv := fiberResidueFieldEquiv f x
  residueFieldEquiv_spec := fiberResidueFieldEquiv_spec f x
  toAddEquiv := fiberTangentEquiv f x
  toAddEquiv_fiberι := fiberTangentEquiv_fiberι f x
  toAddEquiv_smul := fiberTangentEquiv_smul f x

end AlgebraicGeometry

end
