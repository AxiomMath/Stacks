module

public import StacksFrontier.AlgebraicGeometry.Quot.QuotFibreClassifierSpace

/-!
# Morphisms of the 2-fibre product of `Quot_{F/X/B} ⟶ Coh_{X/B}` with a point

Let `y : (Sch/V)_{fppf} ⟶ Coh_{X/B}` be a scheme-valued point.  An object `P` of the 2-fibre
product `(Sch/V) ×_{Coh_{X/B}} Quot_{F/X/B}` carries the surjection `F_T ⟶ y(x)` of
`AlgebraicGeometry.Space.QuotSituation.fibreClassMap`.  This file proves that a morphism
`a : x ⟶ x'` of the first components extends to a morphism of the 2-fibre product as soon as it
carries the surjection of the target to the surjection of the source: the quotient of the source
is then the pullback of the quotient of the target, because a quotient is the kernel of its
projection, and the comparison isomorphisms are compatible because the projections are
epimorphisms.  This is the injectivity of the classifying map in the proof of Stacks 09TU.

## Main results

* `AlgebraicGeometry.Space.QuotSituation.kernelSubobject_pullMapOf_quotientProjection`: the kernel
  of the pullback of the projection onto a quotient is the pulled-back quotient.
* `AlgebraicGeometry.Space.QuotSituation.coherentHom_eq_of_pullMapOf_eq`: two morphisms of
  `Coh_{X/B}` into an object attached to a quotient with the same base map agree as soon as they
  pull the projection onto the quotient back to the same map.
* `AlgebraicGeometry.Space.QuotSituation.exists_hom_of_fibreClassMap_eq`: the extension of a
  morphism of first components to a morphism of the 2-fibre product.

## References

* [Stacks Project, Tag 09TU](https://stacks.math.columbia.edu/tag/09TU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local implicit_reducible] AlgebraicGeometry.Space.QuotSituation.toCoherentSituation

namespace CategoryTheory

/-- A morphism conjugated by identifications in three layers is conjugated by the composite
identifications. -/
theorem eqToHom_conj_conj_eq {C : Type*} [Category* C] {X Y X₁ Y₁ X₂ Y₂ X₃ Y₃ : C}
    (f : X ⟶ Y) (h₁ : X₁ = X₂) (h₂ : X₂ = X₃) (h₃ : X₃ = X) (h₄ : Y = Y₃) (h₅ : Y₃ = Y₂)
    (h₆ : Y₂ = Y₁) (h₇ : X₁ = X) (h₈ : Y = Y₁) :
    eqToHom h₁ ≫ (eqToHom h₂ ≫ (eqToHom h₃ ≫ f ≫ eqToHom h₄) ≫ eqToHom h₅) ≫ eqToHom h₆ =
      eqToHom h₇ ≫ f ≫ eqToHom h₈ := by
  subst_vars
  simp

end CategoryTheory

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace QuotSituation

variable (D : QuotSituation B S hS)

/-- **The kernel of the pullback of the projection onto a quotient is the pulled-back
quotient.** -/
theorem kernelSubobject_pullMapOf_quotientProjection {T' T : SchemesOver D.Y} (h : T' ⟶ T)
    (K : Subobject (D.baseChangeModule T))
    {M' : Modules.{u, u} B S hS (D.space T').1 (D.space T').2}
    (α : (modulePullback B S hS (D.relativeMap h)).obj (D.quotientModule T K) ⟶ M')
    (hα : IsIso α) :
    kernelSubobject (D.pullMapOf h α (D.quotientProjection T K)) = D.quotientPullback h K := by
  rw [pullMapOf_def, ← Category.assoc, kernelSubobject_comp_mono]
  rfl

/-- **The kernel of the pullback of a surjection is the pullback of its kernel.** -/
theorem kernelSubobject_pullMapOf_of_epi {T' T : SchemesOver D.Y} (h : T' ⟶ T)
    {M : Modules.{u, u} B S hS (D.space T).1 (D.space T).2}
    {M' : Modules.{u, u} B S hS (D.space T').1 (D.space T').2}
    (α : (modulePullback B S hS (D.relativeMap h)).obj M ⟶ M') (hα : IsIso α)
    (v : D.baseChangeModule T ⟶ M) (hv : Epi v) :
    kernelSubobject (D.pullMapOf h α v) = D.quotientPullback h (kernelSubobject v) := by
  let e : D.quotientModule T (kernelSubobject v) ≅ M := Abelian.cokernelKernelSubobjectIso v
  have hv' : v = D.quotientProjection T (kernelSubobject v) ≫ e.hom := by
    have h₀ : v ≫ e.inv = D.quotientProjection T (kernelSubobject v) :=
      Abelian.cokernelKernelSubobjectIso_inv_comp v
    rw [← h₀, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hiso : IsIso ((modulePullback B S hS (D.relativeMap h)).map e.hom ≫ α) :=
    @IsIso.comp_isIso _ _ _ _ _ _ _ (Functor.map_isIso _ e.hom) hα
  have heq : D.pullMapOf h α v = D.pullMapOf h
      ((modulePullback B S hS (D.relativeMap h)).map e.hom ≫ α)
      (D.quotientProjection T (kernelSubobject v)) := by
    rw [pullMapOf_def, pullMapOf_def]
    conv_lhs => rw [hv']
    rw [Functor.map_comp]
    simp only [Category.assoc]
  exact (congrArg (fun f => kernelSubobject f) heq).trans
    (D.kernelSubobject_pullMapOf_quotientProjection h (kernelSubobject v) _ hiso)

/-- **Pulling the projection onto a quotient back is injective in the comparison
isomorphism**: the projection is an epimorphism, and so is its inverse image. -/
theorem pullMapOf_quotientProjection_injective {T' T : SchemesOver D.Y} (h : T' ⟶ T)
    (K : Subobject (D.baseChangeModule T))
    {M' : Modules.{u, u} B S hS (D.space T').1 (D.space T').2}
    (α β : (modulePullback B S hS (D.relativeMap h)).obj (D.quotientModule T K) ⟶ M')
    (hαβ : D.pullMapOf h α (D.quotientProjection T K) =
      D.pullMapOf h β (D.quotientProjection T K)) : α = β := by
  have := (modulePullback B S hS (D.relativeMap h)).map_epi (D.quotientProjection T K)
  simpa only [pullMapOf_def, cancel_epi] using hαβ

/-- **Two morphisms of `Coh_{X/B}` into the object attached to a quotient, with the same base map,
agree as soon as they pull the projection onto the quotient back to the same map.** -/
theorem coherentHom_eq_of_pullMapOf_eq {E : CoherentObject D.toCoherentSituation}
    {T : SchemesOver D.Y} {K : Subobject (D.baseChangeModule T)}
    {hK : K ∈ D.properlySupportedQuotients T} (m n : CoherentHom E (D.cohObject T K hK))
    (hb : m.base = n.base)
    (h : D.pullMapOf m.base m.fibre (D.quotientProjection T K) =
      D.pullMapOf n.base n.fibre (D.quotientProjection T K)) : m = n := by
  obtain ⟨mb, mf, mi⟩ := m
  obtain ⟨nb, nf, ni⟩ := n
  change mb = nb at hb
  subst hb
  have hf : mf = nf := D.pullMapOf_quotientProjection_injective mb K mf nf h
  subst hf
  rfl

/-- `AlgebraicGeometry.Space.QuotSituation.coherentHom_eq_of_pullMapOf_eq` for the object of
`Coh_{X/B}` attached to a section of the Quot presheaf. -/
theorem coherentHom_family_eq_of_pullMapOf_eq {E : CoherentObject D.toCoherentSituation}
    {U : BigFppfOver B S hS} {z : QuotFamilyOver D U}
    (m n : CoherentHom E (D.cohObjectOfFamily z)) (hb : m.base = n.base)
    (h : D.pullMapOf m.base m.fibre (D.quotientProjection (D.cohObjectOfFamily z).T z.subobject) =
      D.pullMapOf n.base n.fibre (D.quotientProjection (D.cohObjectOfFamily z).T z.subobject)) :
    m = n :=
  D.coherentHom_eq_of_pullMapOf_eq m n hb h

/-- The morphism of `Coh_{X/B}` attached to a morphism of sections of the Quot presheaf pulls the
projection onto the target quotient back to the projection onto the source quotient. -/
theorem pullMapOf_family_quotientProjection {U' U : BigFppfOver B S hS}
    {x : QuotFamilyOver D U'} {z : QuotFamilyOver D U}
    (k : (D.cohObjectOfFamily x).T ⟶ (D.cohObjectOfFamily z).T)
    (hK : D.quotientPullback k z.subobject = x.subobject)
    (m : CoherentHom (D.cohObjectOfFamily x) (D.cohObjectOfFamily z))
    (hm : m = D.cohHomOfData k hK z.mem x.mem) :
    D.pullMapOf m.base m.fibre (D.quotientProjection (D.cohObjectOfFamily z).T z.subobject) =
      D.quotientProjection (D.cohObjectOfFamily x).T x.subobject := by
  subst hm
  exact D.pullMapOf_quotientFibreIso_quotientProjection k hK

/-- Pulling back with a comparison followed by `γ` is pulling back and then applying `γ`. -/
theorem pullMapOf_comp_right {T' T : SchemesOver D.Y} (h : T' ⟶ T)
    {M : Modules.{u, u} B S hS (D.space T).1 (D.space T).2}
    {M' M'' : Modules.{u, u} B S hS (D.space T').1 (D.space T').2}
    (α : (modulePullback B S hS (D.relativeMap h)).obj M ⟶ M') (γ : M' ⟶ M'')
    (v : D.baseChangeModule T ⟶ M) :
    D.pullMapOf h (α ≫ γ) v = D.pullMapOf h α v ≫ γ := by
  rw [pullMapOf_def, pullMapOf_def]
  simp only [Category.assoc]

/-- A section of the Quot presheaf is the restriction of another along `g` as soon as their
morphisms to the base and their kernels are related by a morphism of test schemes over `g`. -/
theorem quotFamily_eq_baseChange_of {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
    (x : QuotFamilyOver D T') (z : QuotFamilyOver D T)
    (htb : x.toBase = (schemeSpaceFunctor B S hS).map g ≫ z.toBase)
    (k : (CostructuredArrow.mk x.toBase : SchemesOver D.Y) ⟶ CostructuredArrow.mk z.toBase)
    (hk : k.left = g) (hK : x.subobject = D.quotientPullback k z.subobject) :
    x = z.baseChange g := by
  obtain ⟨xb, xs, xm⟩ := x
  change xb = (schemeSpaceFunctor B S hS).map g ≫ z.toBase at htb
  subst htb
  have hk' : k = QuotFamilyOver.restrict g z.toBase := CostructuredArrow.hom_ext _ _ hk
  subst hk'
  exact QuotFamilyOver.ext rfl (heq_of_eq hK)

/-- The inverse of a morphism of test schemes over `B` whose underlying morphism of schemes is an
identification. -/
def testInv {T₁ T₂ : SchemesOver D.Y} (k : T₁ ⟶ T₂) {e : T₁.left = T₂.left}
    (hk : k.left = eqToHom e) : T₂ ⟶ T₁ :=
  CostructuredArrow.homMk (eqToHom e.symm) (by
    rw [← CostructuredArrow.w k, hk, ← Category.assoc, ← CategoryTheory.Functor.map_comp,
      eqToHom_trans, eqToHom_refl, CategoryTheory.Functor.map_id, Category.id_comp])

/-- Composing `testInv k hk` with `k` gives the identity of `T₂`. -/
theorem testInv_comp {T₁ T₂ : SchemesOver D.Y} (k : T₁ ⟶ T₂) {e : T₁.left = T₂.left}
    (hk : k.left = eqToHom e) : D.testInv k hk ≫ k = 𝟙 T₂ :=
  CostructuredArrow.hom_ext _ _ (by
    rw [CostructuredArrow.comp_left, hk]
    simp [testInv])

/-- Composing `k` with `testInv k hk` gives the identity of `T₁`. -/
theorem comp_testInv {T₁ T₂ : SchemesOver D.Y} (k : T₁ ⟶ T₂) {e : T₁.left = T₂.left}
    (hk : k.left = eqToHom e) : k ≫ D.testInv k hk = 𝟙 T₁ :=
  CostructuredArrow.hom_ext _ _ (by
    rw [CostructuredArrow.comp_left, hk]
    simp [testInv])

variable {V : BigFppfOver B S hS}
  (y : (Stack.schemeFibredCategory B S hS V).val ⥤ᵇ D.toCoherentSituation.coherentCFG.val)

/-- The scheme of the test scheme of `y(x)` is the base of the quotient of an object of the 2-fibre
product. -/
theorem fibreQuotBaseEq (P : (D.fibreProduct y).val.obj) : (y.obj P.x).T.left = P.y.base :=
  (D.fibreBaseEq y P).trans P.hy.symm

/-- **The comparison `y(x) ≅ (T, F_T/K)` carried by an object of the 2-fibre product lies over an
identity**, so its base map is an identification. -/
theorem fibreIsoHom_base_left (P : (D.fibreProduct y).val.obj) :
    (D.fibreIsoHom y P).base.left = eqToHom (D.fibreQuotBaseEq y P) := by
  have := P.vertical
  have h := IsHomLift.fac' D.toCoherentSituation.coherentCFG.val.p (𝟙 P.base) P.iso.hom
  refine h.trans ?_
  simp only [Category.id_comp, eqToHom_trans]
  rfl

/-- The morphism of schemes underlying `y(a)` for a morphism `a` of schemes over `V`. -/
theorem fibreMapHom_base_left_of {x' x : Over V} (a : x' ⟶ x) :
    (D.fibreMapHom y a).base.left =
      eqToHom (Functor.congr_obj y.w x') ≫ a.left ≫ eqToHom (Functor.congr_obj y.w x).symm :=
  Functor.congr_hom y.w a

/-- **A morphism of first components extends to a morphism of the 2-fibre product as soon as it
carries the surjection of the target to the surjection of the source.** -/
theorem exists_hom_of_fibreClassMap_eq {P Q : (D.fibreProduct y).val.obj} (a : P.x ⟶ Q.x)
    (h : D.fibreClassMap y P = D.pullMapOf (D.fibreMapHom y a).base (D.fibreMapHom y a).fibre
      (D.fibreClassMap y Q)) :
    ∃ m : P ⟶ Q, m.a = a := by
  have hc := modulePushforwardCoherence B S hS
  let φP := D.fibreIsoHom y P
  let φQ := D.fibreIsoHom y Q
  let ya := D.fibreMapHom y a
  have := φP.isIso_fibre
  have := φQ.isIso_fibre
  have := ya.isIso_fibre
  let ιP := D.testInv φP.base (D.fibreIsoHom_base_left y P)
  let g : (D.cohObjectOfFamily P.y.fiber.as).T ⟶ (D.cohObjectOfFamily Q.y.fiber.as).T :=
    ιP ≫ ya.base ≫ φQ.base
  have hK1 : D.quotientPullback φP.base P.y.fiber.as.subobject =
      D.quotientPullback (ya.base ≫ φQ.base) Q.y.fiber.as.subobject := by
    have e1 := D.kernelSubobject_pullMapOf_quotientProjection φP.base P.y.fiber.as.subobject
      φP.fibre φP.isIso_fibre
    have e2 := D.kernelSubobject_pullMapOf_of_epi ya.base ya.fibre ya.isIso_fibre
      (D.fibreClassMap y Q) (D.epi_fibreClassMap y Q)
    have e3 := D.kernelSubobject_pullMapOf_quotientProjection φQ.base Q.y.fiber.as.subobject
      φQ.fibre φQ.isIso_fibre
    have e4 := congrArg (fun f => kernelSubobject f) h
    exact e1.symm.trans (e4.trans (e2.trans ((congrArg (D.quotientPullback ya.base) e3).trans
      (D.quotientPullback_comp hc ya.base φQ.base Q.y.fiber.as.subobject).symm)))
  have hK : P.y.fiber.as.subobject = D.quotientPullback g Q.y.fiber.as.subobject := by
    have e1 : D.quotientPullback (ιP ≫ φP.base) P.y.fiber.as.subobject =
        P.y.fiber.as.subobject := by
      rw [D.testInv_comp φP.base (D.fibreIsoHom_base_left y P)]
      exact D.quotientPullback_id hc _ _
    refine e1.symm.trans ((D.quotientPullback_comp hc _ _ _).trans ?_)
    rw [hK1]
    exact (D.quotientPullback_comp hc _ _ _).symm
  have htb : P.y.fiber.as.toBase =
      (schemeSpaceFunctor B S hS).map g.left ≫ Q.y.fiber.as.toBase :=
    (CostructuredArrow.w g).symm
  have hfib : P.y.fiber.as = Q.y.fiber.as.baseChange g.left :=
    D.quotFamily_eq_baseChange_of g.left P.y.fiber.as Q.y.fiber.as htb g rfl hK
  let b : P.y ⟶ Q.y := { base := g.left, fiber := Discrete.eqToHom hfib }
  have hgl : g.left = eqToHom (D.fibreQuotBaseEq y P).symm ≫
      (eqToHom (Functor.congr_obj y.w P.x) ≫ a.left ≫ eqToHom (Functor.congr_obj y.w Q.x).symm) ≫
        eqToHom (D.fibreQuotBaseEq y Q) := by
    show ιP.left ≫ ya.base.left ≫ φQ.base.left = _
    rw [D.fibreMapHom_base_left_of y a, D.fibreIsoHom_base_left y Q]
    rfl
  have hbase : eqToHom P.hy.symm ≫ b.base ≫ eqToHom Q.hy =
      eqToHom P.hx.symm ≫ a.left ≫ eqToHom Q.hx := by
    have hbl : b.base = g.left := rfl
    rw [hbl, hgl]
    exact eqToHom_conj_conj_eq _ _ _ _ _ _ _ _ _
  let qb : CoherentHom (D.cohObjectOfFamily P.y.fiber.as) (D.cohObjectOfFamily Q.y.fiber.as) :=
    D.cohHomOfData (D.familyBaseMap b.base Q.y.fiber.as hfib)
      (D.quotientPullback_familyBaseMap b.base Q.y.fiber.as hfib) Q.y.fiber.as.mem
      P.y.fiber.as.mem
  have hqb : qb.base = g := CostructuredArrow.hom_ext _ _ rfl
  have hb : (CoherentHom.comp ya φQ).base = (CoherentHom.comp φP qb).base := by
    show ya.base ≫ φQ.base = φP.base ≫ qb.base
    rw [hqb]
    show ya.base ≫ φQ.base = φP.base ≫ ιP ≫ ya.base ≫ φQ.base
    rw [← Category.assoc φP.base, D.comp_testInv φP.base (D.fibreIsoHom_base_left y P),
      Category.id_comp]
  have hw : CoherentHom.comp ya φQ = CoherentHom.comp φP qb := by
    refine D.coherentHom_family_eq_of_pullMapOf_eq _ _ hb ?_
    refine (D.pullMapOf_comp ya.base φQ.base ya.fibre φQ.fibre _).trans ?_
    refine h.symm.trans ?_
    have e5 := D.pullMapOf_comp φP.base qb.base φP.fibre qb.fibre
      (D.quotientProjection _ Q.y.fiber.as.subobject)
    have e6 := D.pullMapOf_family_quotientProjection
      (D.familyBaseMap b.base Q.y.fiber.as hfib)
      (D.quotientPullback_familyBaseMap b.base Q.y.fiber.as hfib) qb rfl
    exact (congrArg (D.pullMapOf φP.base φP.fibre) e6.symm).trans e5.symm
  exact ⟨TwoFibreProductOver.Hom.mk' a b hbase hw, rfl⟩

end QuotSituation

end AlgebraicGeometry.Space

end
