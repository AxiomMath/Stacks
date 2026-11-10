module

public import StacksFrontier.AlgebraicGeometry.Quot.PicardForgetTrivializationFibre
public import StacksFrontier.CategoryTheory.FiberedInSetoids.EquivalentFiberedInSets
public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack.PullbackFiber

/-!
# Isomorphism classes of the base change of `Picardstack_{X/B, σ} ⟶ Picardstack_{X/B}`

The 2-fibre product of the forgetful 1-morphism `Picardstack_{X/B, σ} ⟶ Picardstack_{X/B}` with a
family `y` of objects of `Picardstack_{X/B}` has, over each index, the trivialisations along `y` as
its isomorphism classes: an object `(V, x, φ : y(V) ≅ x)` names the trivialisation of `x`
transported along `φ`, and this is a natural bijection
(`AlgebraicGeometry.Space.bijective_forgetTrivializationIsoClassMap`).  This is the fibre
identification in the proof of Stacks 0D2A.

## Main definitions

* `AlgebraicGeometry.Space.forgetTrivializationIsoClassMap`: the map from the isomorphism classes
  of the 2-fibre product to the trivialisations along `y`.

## Main results

* `AlgebraicGeometry.Space.bijective_forgetTrivializationIsoClassMap`: that map is bijective.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory.Functor

variable {𝒞 : Type*} [Category* 𝒞] {𝒮 : Type*} [Category* 𝒮] (p : 𝒮 ⥤ 𝒞)
  (X : 𝒞ᵒᵖ ⥤ Type*) (κ₀ : ∀ P : 𝒮, X.obj (op (p.obj P)))

/-- The value of a family of elements on an object of a fibre, transported to the base of the
fibre. -/
def fiberClassValue {V : 𝒞} (P : p.Fiber V) : X.obj (op V) :=
  X.map (eqToHom P.2.symm).op (κ₀ P.1)

/-- Two objects of a fibre with the same value: the value of the second, carried back along the
identification of their underlying objects of the base, is the value of the first. -/
theorem map_eqToHom_of_fiberClassValue_eq {V : 𝒞} (P Q : p.Fiber V)
    (h : fiberClassValue p X κ₀ P = fiberClassValue p X κ₀ Q) :
    X.map (eqToHom (P.2.trans Q.2.symm)).op (κ₀ Q.1) = κ₀ P.1 := by
  obtain ⟨P, hP⟩ := P
  obtain ⟨Q, hQ⟩ := Q
  change p.obj P = V at hP
  change p.obj Q = V at hQ
  subst hP
  simp only [fiberClassValue, eqToHom_refl, op_id, CategoryTheory.Functor.map_id,
    types_id_apply] at h
  rw [h]

variable {p X κ₀}
variable (hκ : ∀ {P Q : 𝒮} (φ : P ⟶ Q), X.map (p.map φ).op (κ₀ Q) = κ₀ P)

include hκ in
/-- A morphism `φ : P ⟶ Q` of `𝒮` over `f` relates the values transported to the bases. -/
theorem fiberClassValue_of_isHomLift {V W : 𝒞} (f : V ⟶ W) (P : p.Fiber V) (Q : p.Fiber W)
    (φ : P.1 ⟶ Q.1) (hφ : p.IsHomLift f φ) :
    fiberClassValue p X κ₀ P = X.map f.op (fiberClassValue p X κ₀ Q) := by
  have hfac := IsHomLift.fac' p f φ
  obtain ⟨P, hP⟩ := P
  obtain ⟨Q, hQ⟩ := Q
  change p.obj P = V at hP
  change p.obj Q = W at hQ
  subst hP hQ
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hfac
  simp only [fiberClassValue, eqToHom_refl, op_id, CategoryTheory.Functor.map_id, types_id_apply]
  rw [← hκ φ, hfac]

include hκ in
/-- Isomorphic objects of a fibre have the same value. -/
theorem fiberClassValue_eq_of_hom {V : 𝒞} {P Q : p.Fiber V} (i : P ⟶ Q) :
    fiberClassValue p X κ₀ P = fiberClassValue p X κ₀ Q := by
  rw [fiberClassValue_of_isHomLift hκ (𝟙 V) P Q (Fiber.fiberInclusion.map i) i.2, op_id,
    CategoryTheory.Functor.map_id, types_id_apply]

/-- **The map on isomorphism classes induced by a compatible family.** -/
def isoClassLiftOfCompatible [p.IsFibered] (V : 𝒞) :
    p.isoClassPresheaf.obj (op V) → X.obj (op V) :=
  _root_.Quotient.lift (fiberClassValue p X κ₀) (fun _ _ h ↦
    fiberClassValue_eq_of_hom hκ ((isIsomorphicSetoid_r_iff _ _).1 h).some.hom)

/-- The map on isomorphism classes sends the class of an object to its value. -/
theorem isoClassLiftOfCompatible_mk [p.IsFibered] {V : 𝒞} (P : p.Fiber V) :
    isoClassLiftOfCompatible hκ V (isoClassMk p P) = fiberClassValue p X κ₀ P :=
  rfl

/-- The map on isomorphism classes is natural. -/
theorem isoClassLiftOfCompatible_naturality [p.IsFibered] {V W : 𝒞} (f : V ⟶ W)
    (c : p.isoClassPresheaf.obj (op W)) :
    isoClassLiftOfCompatible hκ V (p.isoClassPresheaf.map f.op c) =
      X.map f.op (isoClassLiftOfCompatible hκ W c) := by
  induction c using _root_.Quotient.ind with
  | _ x =>
    change isoClassLiftOfCompatible hκ V (p.isoClassPresheaf.map f.op (isoClassMk p x)) = _
    rw [isoClassPresheaf_map_isoClassMk, isoClassLiftOfCompatible_mk]
    exact fiberClassValue_of_isHomLift hκ f _ x (IsPreFibered.pullbackMap x.2 f)
      (IsPreFibered.pullbackMap.IsCartesian x.2 f).toIsHomLift

omit p in
/-- A composite of three `eqToHom`s is an `eqToHom`. -/
theorem _root_.CategoryTheory.eqToHom_comp_eqToHom_comp_eqToHom {a b c d : 𝒞} (h₁ : a = b)
    (h₂ : b = c) (h₃ : c = d) :
    eqToHom h₁ ≫ eqToHom h₂ ≫ eqToHom h₃ = eqToHom (h₁.trans (h₂.trans h₃)) := by
  simp

/-- An isomorphism lying over an identity is mapped to identities, up to `eqToHom`. -/
theorem exists_map_eq_eqToHom_of_isHomLift_id {U : 𝒞} {a b : 𝒮} (e : a ≅ b)
    (he : p.IsHomLift (𝟙 U) e.hom) :
    ∃ h : p.obj a = p.obj b, p.map e.hom = eqToHom h ∧ p.map e.inv = eqToHom h.symm := by
  have h1 : p.map e.hom = eqToHom ((IsHomLift.domain_eq p (𝟙 U) e.hom).trans
      (IsHomLift.codomain_eq p (𝟙 U) e.hom).symm) := by
    rw [IsHomLift.fac' p (𝟙 U) e.hom]
    simp
  refine ⟨_, h1, ?_⟩
  rw [← cancel_mono (p.map e.hom), ← Functor.map_comp, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, h1]
  simp

end CategoryTheory.Functor

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {s : PicardSituation B S hS} (σ : s.base ⟶ s.X) (hσ : σ ≫ s.f = 𝟙 s.base)
  (hc : ModulePushforwardCoherence B S hS)

section Fibre

variable {𝒯 : Type*} [Category* 𝒯] (P𝒯 : 𝒯 ⥤ BigFppfOver B S hS)
  (y : 𝒯 ⥤ (picardCFG hc s).val.obj)

/-- The 2-fibre product of the forgetful 1-morphism of Stacks 0D2A with a family `y` of objects of
`Picardstack_{X/B}` indexed by a category over the site. -/
abbrev forgetTrivializationFibre :=
  TwoFibreProductOver P𝒯 (sectionedPicardCFG hc (sectionTransportCoherence hc σ hσ)).val.p
    (picardCFG hc s).val.p y
    (forgetTrivialization hc (sectionTransportCoherence hc σ hσ)).hom.toFunctor

/-- The first projection of `forgetTrivializationFibre`. -/
abbrev forgetTrivializationFibreFst :=
  TwoFibreProductOver.fst P𝒯 (sectionedPicardCFG hc (sectionTransportCoherence hc σ hσ)).val.p
    (picardCFG hc s).val.p y
    (forgetTrivialization hc (sectionTransportCoherence hc σ hσ)).hom.toFunctor

/-- The morphisms of the family `y`, read as morphisms of `Picardstack_{X/B}`. -/
abbrev familyMap {V W : 𝒯} (g : V ⟶ W) : PicardHom (y.obj V) (y.obj W) := y.map g

/-- The family `y` preserves identities. -/
theorem familyMap_id (V : 𝒯) : familyMap hc y (𝟙 V) = PicardHom.id hc (y.obj V) :=
  y.map_id V

/-- The family `y` preserves composition. -/
theorem familyMap_comp {V W Z : 𝒯} (f : V ⟶ W) (g : W ⟶ Z) :
    familyMap hc y (f ≫ g) = PicardHom.comp (familyMap hc y f) (familyMap hc y g) :=
  y.map_comp f g

/-- The identities of `Picardstack_{X/B}` as a category fibred in groupoids. -/
theorem picardCFG_id_eq (A : (picardCFG hc s).val.obj) :
    (𝟙 A : A ⟶ A) = PicardHom.id hc A :=
  rfl

/-- The trivialisations along the family `y`. -/
abbrev trivializationsAlongFamily : 𝒯ᵒᵖ ⥤ Type (u + 1) :=
  trivializationsAlong σ hσ hc y.obj (familyMap hc y) (familyMap_id hc y) (familyMap_comp hc y)

/-- The trivialisation named by an object `(V, x, φ : y(V) ≅ F(x))` of the 2-fibre product: the
trivialisation of `x`, transported along `φ`. -/
def fibreTrivialization (P : forgetTrivializationFibre σ hσ hc P𝒯 y) :
    (trivializationsAlongFamily σ hσ hc y).obj (op P.x) :=
  PicardSituation.transportTrivializationIso (σ := σ) (hσ := hσ)
    (show PicardHom (y.obj P.x) P.y.toPicardObject from P.iso.hom) P.y.trivialization

/-- The underlying morphism of `AlgebraicGeometry.Space.fibreTrivialization`. -/
theorem fibreTrivialization_hom (P : forgetTrivializationFibre σ hσ hc P𝒯 y) :
    (fibreTrivialization σ hσ hc P𝒯 y P).hom =
      PicardSituation.transportTrivialization (σ := σ) (hσ := hσ)
        (show PicardHom (y.obj P.x) P.y.toPicardObject from P.iso.hom) P.y.trivialization.hom :=
  PicardSituation.transportTrivializationIso_hom (σ := σ) (hσ := hσ) _ _

/-- **The trivialisation named by an object of the 2-fibre product is compatible with the
morphisms of the 2-fibre product.** -/
theorem fibreTrivialization_map {P Q : forgetTrivializationFibre σ hσ hc P𝒯 y} (φ : P ⟶ Q) :
    (trivializationsAlongFamily σ hσ hc y).map
        ((forgetTrivializationFibreFst σ hσ hc P𝒯 y).map φ).op
        (fibreTrivialization σ hσ hc P𝒯 y Q) = fibreTrivialization σ hσ hc P𝒯 y P := by
  refine (trivializationsAlong_map_apply σ hσ hc y.obj (familyMap hc y) (familyMap_id hc y)
    (familyMap_comp hc y) _ _).trans (Iso.ext ?_)
  have hw : PicardHom.comp (familyMap hc y
      ((forgetTrivializationFibreFst σ hσ hc P𝒯 y).map φ).op.unop)
      (show PicardHom (y.obj Q.x) Q.y.toPicardObject
      from Q.iso.hom) = PicardHom.comp (show PicardHom (y.obj P.x) P.y.toPicardObject
      from P.iso.hom) φ.b.toPicardHom := φ.w
  refine (PicardSituation.transportTrivializationIso_hom _ _).trans ?_
  rw [fibreTrivialization_hom, fibreTrivialization_hom]
  refine (PicardSituation.sectionTransportCoherence_transport_comp σ hσ hc _ _ _).symm.trans ?_
  rw [hw]
  refine (PicardSituation.sectionTransportCoherence_transport_comp σ hσ hc _ _ _).trans ?_
  exact congrArg _ φ.b.compatible

/-- **The isomorphism classes of the 2-fibre product name trivialisations along `y`.** -/
def forgetTrivializationIsoClassMap [(forgetTrivializationFibreFst σ hσ hc P𝒯 y).IsFibered]
    (V : 𝒯) : (forgetTrivializationFibreFst σ hσ hc P𝒯 y).isoClassPresheaf.obj (op V) →
      (trivializationsAlongFamily σ hσ hc y).obj (op V) :=
  Functor.isoClassLiftOfCompatible (fibreTrivialization_map σ hσ hc P𝒯 y) V

/-- The isomorphism-class map is natural. -/
theorem forgetTrivializationIsoClassMap_naturality
    [(forgetTrivializationFibreFst σ hσ hc P𝒯 y).IsFibered] {V W : 𝒯} (f : V ⟶ W)
    (c : (forgetTrivializationFibreFst σ hσ hc P𝒯 y).isoClassPresheaf.obj (op W)) :
    forgetTrivializationIsoClassMap σ hσ hc P𝒯 y V
        ((forgetTrivializationFibreFst σ hσ hc P𝒯 y).isoClassPresheaf.map f.op c) =
      (trivializationsAlongFamily σ hσ hc y).map f.op
        (forgetTrivializationIsoClassMap σ hσ hc P𝒯 y W c) :=
  Functor.isoClassLiftOfCompatible_naturality (fibreTrivialization_map σ hσ hc P𝒯 y) f c

variable {P𝒯 y}

/-- The object `(V, (y(V), β), 𝟙)` of the 2-fibre product attached to a trivialisation `β`. -/
def fibreObjectOfTrivialization (hy : y ⋙ (picardCFG hc s).val.p = P𝒯) (V : 𝒯)
    (β : (trivializationsAlongFamily σ hσ hc y).obj (op V)) :
    forgetTrivializationFibre σ hσ hc P𝒯 y where
  base := P𝒯.obj V
  x := V
  y := ⟨y.obj V, β⟩
  hx := rfl
  hy := Functor.congr_obj hy V
  iso := Iso.refl _
  vertical := IsHomLift.id (Functor.congr_obj hy V)

/-- The object of the 2-fibre product attached to a trivialisation names that
trivialisation. -/
theorem fibreTrivialization_fibreObjectOfTrivialization (hy : y ⋙ (picardCFG hc s).val.p = P𝒯)
    (V : 𝒯) (β : (trivializationsAlongFamily σ hσ hc y).obj (op V)) :
    fibreTrivialization σ hσ hc P𝒯 y (fibreObjectOfTrivialization σ hσ hc hy V β) = β := by
  apply Iso.ext
  refine (fibreTrivialization_hom σ hσ hc P𝒯 y _).trans ?_
  have h1 : (show PicardHom (y.obj V) (y.obj V) from (Iso.refl (y.obj V)).hom) =
      PicardHom.id hc (y.obj V) := picardCFG_id_eq hc (y.obj V)
  refine (congrArg (fun m ↦ PicardSituation.transportTrivialization (σ := σ) (hσ := hσ) m
    β.hom) h1).trans ?_
  exact PicardSituation.sectionTransportCoherence_transport_id σ hσ hc _ β.hom

variable (P𝒯 y) in
/-- **Objects of a fibre of the 2-fibre product naming the same trivialisation are isomorphic.** -/
theorem nonempty_iso_of_fiberClassValue_eq
    (hfib : (forgetTrivializationFibreFst σ hσ hc P𝒯 y).IsFiberedInGroupoids) {V : 𝒯}
    (P Q : (forgetTrivializationFibreFst σ hσ hc P𝒯 y).Fiber V)
    (h : Functor.fiberClassValue _ _ (fibreTrivialization σ hσ hc P𝒯 y) P =
      Functor.fiberClassValue _ _ (fibreTrivialization σ hσ hc P𝒯 y) Q) :
    Nonempty (P ≅ Q) := by
  have hv := Functor.map_eqToHom_of_fiberClassValue_eq _ _ _ P Q h
  set e : P.1.x = Q.1.x := P.2.trans Q.2.symm
  have h2 := (trivializationsAlong_map_apply σ hσ hc y.obj (familyMap hc y) (familyMap_id hc y)
    (familyMap_comp hc y) (eqToHom e).op (fibreTrivialization σ hσ hc P𝒯 y Q.1)).symm.trans hv
  have h3 := (PicardSituation.transportTrivializationIso_hom (σ := σ) (hσ := hσ) _ _).symm.trans
    (congrArg Iso.hom h2)
  have hcompat : PicardSituation.transportTrivialization (σ := σ) (hσ := hσ)
      (PicardHom.comp (familyMap hc y (eqToHom e).op.unop)
        (show PicardHom (y.obj Q.1.x) Q.1.y.toPicardObject from Q.1.iso.hom))
      Q.1.y.trivialization.hom =
    PicardSituation.transportTrivialization (σ := σ) (hσ := hσ)
      (show PicardHom (y.obj P.1.x) P.1.y.toPicardObject from P.1.iso.hom)
      P.1.y.trivialization.hom :=
    (PicardSituation.sectionTransportCoherence_transport_comp σ hσ hc _ _ _).trans
      ((congrArg _ (fibreTrivialization_hom σ hσ hc P𝒯 y Q.1).symm).trans
        (h3.trans (fibreTrivialization_hom σ hσ hc P𝒯 y P.1)))
  let m : PicardHom P.1.y.toPicardObject Q.1.y.toPicardObject :=
    PicardHom.comp (show PicardHom P.1.y.toPicardObject (y.obj P.1.x) from P.1.iso.inv)
      (PicardHom.comp (familyMap hc y (eqToHom e).op.unop)
        (show PicardHom (y.obj Q.1.x) Q.1.y.toPicardObject from Q.1.iso.hom))
  have hm : PicardSituation.transportTrivialization (σ := σ) (hσ := hσ) m
      Q.1.y.trivialization.hom = P.1.y.trivialization.hom := by
    refine (PicardSituation.sectionTransportCoherence_transport_comp σ hσ hc _ _ _).trans ?_
    rw [hcompat]
    refine (PicardSituation.sectionTransportCoherence_transport_comp σ hσ hc _ _ _).symm.trans ?_
    have hinv : PicardHom.comp (show PicardHom P.1.y.toPicardObject (y.obj P.1.x) from P.1.iso.inv)
        (show PicardHom (y.obj P.1.x) P.1.y.toPicardObject from P.1.iso.hom) =
          PicardHom.id hc P.1.y.toPicardObject := P.1.iso.inv_hom_id
    rw [hinv]
    exact PicardSituation.sectionTransportCoherence_transport_id σ hσ hc _ _
  let b : P.1.y ⟶ Q.1.y := (⟨m, hm⟩ : PicardSituation.SectionedPicardHom P.1.y Q.1.y)
  obtain ⟨hP, hvP, hvP'⟩ := Functor.exists_map_eq_eqToHom_of_isHomLift_id P.1.iso P.1.vertical
  obtain ⟨hQ, hvQ, -⟩ := Functor.exists_map_eq_eqToHom_of_isHomLift_id Q.1.iso Q.1.vertical
  have hb' : ((sectionedPicardCFG hc (sectionTransportCoherence hc σ hσ)).val.p).map b =
      ((picardCFG hc s).val.p).map P.1.iso.inv ≫
        ((picardCFG hc s).val.p).map (y.map (eqToHom e)) ≫
          ((picardCFG hc s).val.p).map Q.1.iso.hom := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    rfl
  have hbe : ((picardCFG hc s).val.p).map P.1.iso.inv ≫
      ((picardCFG hc s).val.p).map (y.map (eqToHom e)) ≫
        ((picardCFG hc s).val.p).map Q.1.iso.hom =
      eqToHom (hP.symm.trans ((congrArg (fun x ↦ ((picardCFG hc s).val.p).obj (y.obj x)) e).trans
        hQ)) := by
    rw [hvP', hvQ, eqToHom_map, eqToHom_map]
    simp
  let ψ : P.1 ⟶ Q.1 := TwoFibreProductOver.Hom.mk' (eqToHom e) b (by
      refine (congrArg (fun k ↦ eqToHom P.1.hy.symm ≫ k ≫ eqToHom Q.1.hy) (hb'.trans hbe)).trans ?_
      refine (eqToHom_comp_eqToHom_comp_eqToHom _ _ _).trans ?_
      rw [eqToHom_map]
      simp) (by
      change y.map (eqToHom e) ≫ Q.1.iso.hom =
        P.1.iso.hom ≫ (P.1.iso.inv ≫ y.map (eqToHom e) ≫ Q.1.iso.hom)
      rw [Iso.hom_inv_id_assoc])
  have hψ : (forgetTrivializationFibreFst σ hσ hc P𝒯 y).IsHomLift (𝟙 V) ψ :=
    IsHomLift.of_fac' _ _ _ P.2 Q.2 (by
      change eqToHom e = _
      rw [Category.id_comp, eqToHom_trans]
      rfl)
  have : IsIso ψ := by
    have := hfib.isStronglyCartesian_homLift (𝟙 V) ψ
    exact Functor.IsStronglyCartesian.isIso_of_base_isIso
      (p := forgetTrivializationFibreFst σ hσ hc P𝒯 y) (f := 𝟙 V) ψ
  exact ⟨Functor.Fiber.isoMk (asIso ψ) hψ⟩

variable (P𝒯 y) in
/-- **The isomorphism classes of the 2-fibre product are the trivialisations along `y`.** -/
theorem bijective_forgetTrivializationIsoClassMap
    [(forgetTrivializationFibreFst σ hσ hc P𝒯 y).IsFibered]
    (hfib : (forgetTrivializationFibreFst σ hσ hc P𝒯 y).IsFiberedInGroupoids)
    (hy : y ⋙ (picardCFG hc s).val.p = P𝒯) (V : 𝒯) :
    Function.Bijective (forgetTrivializationIsoClassMap σ hσ hc P𝒯 y V) := by
  refine ⟨fun c d hcd ↦ ?_, fun β ↦ ?_⟩
  · obtain ⟨P, rfl⟩ := Functor.isoClassMk_surjective c
    obtain ⟨Q, rfl⟩ := Functor.isoClassMk_surjective d
    obtain ⟨i⟩ := nonempty_iso_of_fiberClassValue_eq σ hσ hc P𝒯 y hfib P Q hcd
    exact Functor.isoClassMk_eq_of_iso i
  · refine ⟨Functor.isoClassMk _ ⟨fibreObjectOfTrivialization σ hσ hc hy V β, rfl⟩, ?_⟩
    change (trivializationsAlongFamily σ hσ hc y).map (eqToHom rfl).op
      (fibreTrivialization σ hσ hc P𝒯 y (fibreObjectOfTrivialization σ hσ hc hy V β)) = β
    rw [eqToHom_refl, op_id, CategoryTheory.Functor.map_id, types_id_apply]
    exact fibreTrivialization_fibreObjectOfTrivialization σ hσ hc hy V β

end Fibre

end AlgebraicGeometry.Space
