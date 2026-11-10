module

public import StacksFrontier.AlgebraicGeometry.Stacks.Algebraic.MorphismRepresentableBySpaces.Basic
public import StacksFrontier.AlgebraicGeometry.Stacks.Algebraic.RepresentableBySpace.Characterization
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentabilityPostcomp
public import StacksFrontier.CategoryTheory.FiberedCategory.PairIsoClassPresheaf
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Comp
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.FibreFunctors
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.MorphismCriterion
public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizationTriangle
import StacksCore.Tactic.StacksAttribute

/-!
# A criterion for a 1-morphism to be representable by algebraic spaces

A 1-morphism of categories fibred in groupoids over the big fppf site of a scheme is
representable by algebraic spaces exactly when it is faithful on every fibre and, for every
object of the target over a scheme `U`, the presheaf on the big fppf site of `U` of
isomorphism classes of pairs (an object upstairs, an isomorphism from the pulled-back object
to its image) is an algebraic space.

The proof is the one in the source: the 2-fibre product with a scheme-valued point of the
target is a category fibred in groupoids whose fibres are setoids precisely when the fibre
functors are faithful, and whose presheaf of isomorphism classes is the presheaf of pairs;
the characterization of the categories fibred in groupoids representable by an algebraic
space then applies to it.

## Main definitions

* `AlgebraicGeometry.IsAlgebraicSpacePairIsoClassPresheaf`: the presheaf of isomorphism
  classes of pairs is an algebraic space, with the comparison to a small algebraic-space
  presheaf as part of the data.

## Main results

* `AlgebraicGeometry.isRepresentableByAlgebraicSpaces_iff_associatedMap`: the criterion.

## Implementation notes

The presheaf of pairs is formed on the slice of the big fppf category over `U` and then
transported to the big fppf category of schemes over the underlying scheme of `U` along the
canonical equivalence between the iterated slice and that slice. Because it may land in a
larger universe than the site, it is compared with a small algebraic-space presheaf pointwise
and naturally rather than by an equality of presheaves. As in the source, the criterion
quantifies over a choice of pullbacks for the target fibration.

## References

* [Stacks Project, Tag 02ZY](https://stacks.math.columbia.edu/tag/02ZY)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor


namespace AlgebraicGeometry

universe baseObj baseHom objA objY objD homA homY homD uAux vAux

/-- A cast morphism factors as any pair of cast morphisms through an intermediate object. -/
private theorem eqToHom_eq_eqToHom_comp_eqToHom {Z : Type uAux} [Category.{vAux} Z]
    {X Y W : Z} (h : X = W) (h₁ : X = Y) (h₂ : Y = W) :
    eqToHom h = eqToHom h₁ ≫ eqToHom h₂ := by
  subst h₁
  subst h₂
  simp

variable {Base : Type baseObj} [Category.{baseHom} Base]

private theorem fiberHom_injective_of_fst_isFiberedInSetoids
    {C : Type baseObj} [Category.{baseHom} C]
    {T : Type objA} [Category.{homA} T]
    {A : Type objY} [Category.{homY} A]
    {Y : Type objD} [Category.{homD} Y]
    (pT : T ⥤ C) (pA : A ⥤ C) (pY : Y ⥤ C)
    (G : T ⥤ Y) (F : A ⥤ Y)
    (hF : F ⋙ pY = pA)
    (hpA : pA.IsFiberedInGroupoids)
    (hsetoid : (TwoFibreProductOver.fst pT pA pY G F).IsFiberedInSetoids)
    (U : C) (t : T) (ht : pT.obj t = U)
    {a b : pA.Fiber U} (ξ : G.obj t ≅ F.obj (Fiber.fiberInclusion.obj b))
    (hξ : pY.IsHomLift (𝟙 U) ξ.hom)
    (φ φ' : a ⟶ b)
    (hφ : F.map (Fiber.fiberInclusion.map φ) =
      F.map (Fiber.fiberInclusion.map φ')) : φ = φ' := by
  let p := TwoFibreProductOver.fst pT pA pY G F
  let x := Fiber.fiberInclusion.obj a
  let x' := Fiber.fiberInclusion.obj b
  let φ₀ := Fiber.fiberInclusion.map φ
  let φ₀' := Fiber.fiberInclusion.map φ'
  have : IsGroupoid (pA.Fiber U) := hpA.fiber_isGroupoid U
  let φIso : Fiber.fiberInclusion.obj a ≅ Fiber.fiberInclusion.obj b := asIso φ₀
  let ξa : G.obj t ≅ F.obj x := ξ ≪≫ (F.mapIso φIso).symm
  have hφ₀ : pA.IsHomLift (𝟙 U) φ₀ := φ.2
  have hφ₀' : pA.IsHomLift (𝟙 U) φ₀' := φ'.2
  have hFφ : pY.IsHomLift (𝟙 U) (F.map φ₀) :=
    Functor.isHomLift_map_of_comp_eq hF (𝟙 U) φ₀
  have hFφ' : pY.IsHomLift (𝟙 U) (F.map φ₀') :=
    Functor.isHomLift_map_of_comp_eq hF (𝟙 U) φ₀'
  have hφIsoInv : pA.IsHomLift (𝟙 U) φIso.inv := by
    have : pA.IsHomLift (𝟙 U) φIso.hom := hφ₀
    exact IsHomLift.lift_id_inv pA U φIso
  have hξa : pY.IsHomLift (𝟙 U) ξa.hom := by
    have hFφinv : pY.IsHomLift (𝟙 U) (F.map φIso.inv) :=
      Functor.isHomLift_map_of_comp_eq hF (𝟙 U) φIso.inv
    exact IsHomLift.comp_lift_id_right pY (𝟙 U) ξ.hom (F.map φIso.inv)
  let P : TwoFibreProductOver pT pA pY G F :=
    { base := U, x := t, y := x, hx := ht, hy := a.2,
      iso := ξa, vertical := hξa }
  let Q : TwoFibreProductOver pT pA pY G F :=
    { base := U, x := t, y := x', hx := ht, hy := b.2,
      iso := ξ, vertical := hξ }
  have hta : pT.IsHomLift (𝟙 U) (𝟙 t) :=
    IsHomLift.of_fac' pT (𝟙 U) (𝟙 t) ht ht (by simp)
  let Φ : P ⟶ Q :=
    { hbase := 𝟙 U, a := 𝟙 t, b := φ₀,
      ha := hta, hb := hφ₀,
      w := by simp [Q, P, ξa, φIso, φ₀] }
  let Φ' : P ⟶ Q :=
    { hbase := 𝟙 U, a := 𝟙 t, b := φ₀',
      ha := hta, hb := hφ₀',
      w := by simp [Q, P, ξa, φIso, φ₀, hφ] }
  let : p.IsHomLift (𝟙 t) Φ := IsHomLift.map p Φ
  let : p.IsHomLift (𝟙 t) Φ' := IsHomLift.map p Φ'
  let P' : p.Fiber t := ⟨P, rfl⟩
  let Q' : p.Fiber t := ⟨Q, rfl⟩
  have hthin := hsetoid.fiber_isThin t
  have : Subsingleton (P' ⟶ Q') := hthin P' Q'
  have hEq : (Fiber.homMk p t Φ) = Fiber.homMk p t Φ' := Subsingleton.elim _ _
  have hEq' : Φ = Φ' := by simpa using congrArg Fiber.fiberInclusion.map hEq
  have hEqb : φ₀ = φ₀' := by simpa [Φ, Φ'] using congrArg TwoFibreProductOver.Hom.b hEq'
  exact Fiber.fiberInclusion.map_injective hEqb

attribute [local implicit_reducible] Functor.Fiber Functor.Fiber.fiberInclusion
  TwoFibreProductOver.fst

private theorem fst_fiberHom_b_isHomLift
    {C : Type baseObj} [Category.{baseHom} C]
    {T : Type objA} [Category.{homA} T]
    {A : Type objY} [Category.{homY} A]
    {Y : Type objD} [Category.{homD} Y]
    (pT : T ⥤ C) (pA : A ⥤ C) (pY : Y ⥤ C)
    (G : T ⥤ Y) (F : A ⥤ Y) {V : T}
    {P Q : (TwoFibreProductOver.fst pT pA pY G F).Fiber V} (w : P ⟶ Q) :
    pA.IsHomLift (𝟙 (pT.obj V)) (Fiber.fiberInclusion.map w).b := by
  let p := TwoFibreProductOver.fst pT pA pY G F
  let w₀ := Fiber.fiberInclusion.map w
  let : p.IsHomLift (𝟙 V) w₀ := w.2
  let xP : pA.Fiber (pT.obj V) :=
    ⟨P.1.y, P.1.hy.trans (P.1.hx.symm.trans (congrArg pT.obj P.2))⟩
  let xQ : pA.Fiber (pT.obj V) :=
    ⟨Q.1.y, Q.1.hy.trans (Q.1.hx.symm.trans (congrArg pT.obj Q.2))⟩
  have hbase : w₀.hbase = eqToHom P.1.hy.symm ≫ eqToHom xP.2 ≫
      𝟙 (pT.obj V) ≫ eqToHom xQ.2.symm ≫ eqToHom Q.1.hy := by
    have hwa : w₀.a = eqToHom P.2 ≫ 𝟙 V ≫ eqToHom Q.2.symm := IsHomLift.fac' p (𝟙 V) w₀
    calc
      w₀.hbase = eqToHom P.1.hx.symm ≫ pT.map w₀.a ≫ eqToHom Q.1.hx :=
        TwoFibreProductOver.Hom.hbase_eq w₀
      _ = eqToHom P.1.hy.symm ≫ eqToHom xP.2 ≫
          𝟙 (pT.obj V) ≫ eqToHom xQ.2.symm ≫ eqToHom Q.1.hy := by
        rw [hwa]
        simp [xP, xQ, eqToHom_map, eqToHom_trans]
  have : pA.IsHomLift w₀.hbase w₀.b := w₀.hb
  have hmap : pA.map w₀.b = eqToHom xP.2 ≫ 𝟙 (pT.obj V) ≫ eqToHom xQ.2.symm := by
    calc
      pA.map w₀.b = eqToHom P.1.hy ≫ w₀.hbase ≫ eqToHom Q.1.hy.symm := by
        simpa using IsHomLift.fac' pA w₀.hbase w₀.b
      _ = eqToHom xP.2 ≫ 𝟙 (pT.obj V) ≫ eqToHom xQ.2.symm := by
        rw [hbase]
        simp [xP, xQ, eqToHom_trans]
  exact IsHomLift.of_fac' pA (𝟙 (pT.obj V)) w₀.b xP.2 xQ.2 hmap

private theorem fst_fiber_isThin_of_faithful
    {C : Type baseObj} [Category.{baseHom} C]
    {T : Type objA} [Category.{homA} T]
    {A : Type objY} [Category.{homY} A]
    {Y : Type objD} [Category.{homD} Y]
    (pT : T ⥤ C) (pA : A ⥤ C) (pY : Y ⥤ C)
    (G : T ⥤ Y) (F : A ⥤ Y)
    (hF : F ⋙ pY = pA)
    (hfaithful : ∀ U : C, (Stacks.RepresentableMorphism.inducedFiberFunctor pA pY F hF U).Faithful)
    (V : T) : Quiver.IsThin ((TwoFibreProductOver.fst pT pA pY G F).Fiber V) := by
  intro A B
  constructor
  intro u v
  let p := TwoFibreProductOver.fst pT pA pY G F
  let u₀ := Fiber.fiberInclusion.map u
  let v₀ := Fiber.fiberInclusion.map v
  let : p.IsHomLift (𝟙 V) u₀ := u.2
  let : p.IsHomLift (𝟙 V) v₀ := v.2
  have ha : u₀.a = v₀.a := by
    have hu := IsHomLift.fac' p (𝟙 V) u₀
    have hv := IsHomLift.fac' p (𝟙 V) v₀
    change u₀.a = v₀.a
    simpa [p] using hu.trans hv.symm
  let xP : pA.Fiber (pT.obj V) :=
    ⟨A.1.y, A.1.hy.trans (A.1.hx.symm.trans (congrArg pT.obj A.2))⟩
  let xQ : pA.Fiber (pT.obj V) :=
    ⟨B.1.y, B.1.hy.trans (B.1.hx.symm.trans (congrArg pT.obj B.2))⟩
  have hFuv : F.map u₀.b = F.map v₀.b := by
    have hh : A.1.iso.hom ≫ F.map u₀.b = A.1.iso.hom ≫ F.map v₀.b := by
      calc
        _ = G.map u₀.a ≫ B.1.iso.hom := u₀.w.symm
        _ = G.map v₀.a ≫ B.1.iso.hom := by rw [ha]
        _ = _ := v₀.w
    exact (cancel_epi A.1.iso.hom).1 hh
  let : pA.IsHomLift (𝟙 (pT.obj V)) u₀.b := fst_fiberHom_b_isHomLift pT pA pY G F u
  let : pA.IsHomLift (𝟙 (pT.obj V)) v₀.b := fst_fiberHom_b_isHomLift pT pA pY G F v
  let φu : xP ⟶ xQ := Fiber.homMk pA (pT.obj V) u₀.b
  let φv : xP ⟶ xQ := Fiber.homMk pA (pT.obj V) v₀.b
  have hmap :
      (Stacks.RepresentableMorphism.inducedFiberFunctor pA pY F hF (pT.obj V)).map φu =
        (Stacks.RepresentableMorphism.inducedFiberFunctor pA pY F hF (pT.obj V)).map φv :=
    (Stacks.RepresentableMorphism.inducedFiberFunctor_map_eq_iff pA pY F hF
      (pT.obj V) φu φv).2 hFuv
  have hφ : φu = φv := (hfaithful (pT.obj V)).map_injective hmap
  have hb : u.1.b = v.1.b := by
    have h := congrArg (Fiber.fiberInclusion.map) hφ
    simp only [φu, φv] at h
    change u₀.b = v₀.b
    exact h
  exact Subtype.ext (TwoFibreProductOver.Hom.ext' ha hb)

private theorem fst_isFiberedInSetoids_of_faithful
    {C : Type baseObj} [Category.{baseHom} C]
    {T : Type objA} [Category.{homA} T]
    {A : Type objY} [Category.{homY} A]
    {Y : Type objD} [Category.{homD} Y]
    (pT : T ⥤ C) (pA : A ⥤ C) (pY : Y ⥤ C)
    (G : T ⥤ Y) (F : A ⥤ Y)
    (hF : F ⋙ pY = pA)
    (hP : (TwoFibreProductOver.fst pT pA pY G F).IsFiberedInGroupoids)
    (hfaithful :
      ∀ U : C, (Stacks.RepresentableMorphism.inducedFiberFunctor pA pY F hF U).Faithful) :
    (TwoFibreProductOver.fst pT pA pY G F).IsFiberedInSetoids :=
  { isFiberedInGroupoids := hP
    fiber_isThin := fst_fiber_isThin_of_faithful pT pA pY G F hF hfaithful }

private theorem isoClassMk_inducedFiberFunctor_pullbackFiber
    {C : Type baseObj} [Category.{baseHom} C]
    {S : Type objA} [Category.{homA} S]
    {T : Type objA} [Category.{homY} T]
    (p : S ⥤ C) (q : T ⥤ C) [p.IsFibered] [q.IsFibered]
    (hq : q.IsFiberedInGroupoids) (Φ : S ⥤ T) (hΦ : Φ ⋙ q = p)
    {V W : C} (f : V ⟶ W) (a : p.Fiber W) :
    Functor.isoClassMk q ((Stacks.RepresentableMorphism.inducedFiberFunctor p q Φ hΦ V).obj
        (Functor.pullbackFiber p a f)) =
      q.isoClassPresheaf.map f.op (Functor.isoClassMk q
        ((Stacks.RepresentableMorphism.inducedFiberFunctor p q Φ hΦ W).obj a)) := by
  rw [Functor.isoClassPresheaf_map_isoClassMk]
  let χ := IsPreFibered.pullbackMap a.2 f
  have hχq : q.IsHomLift f (Φ.map χ) := Functor.isHomLift_map_of_comp_eq hΦ f χ
  have hcart : q.IsCartesian f (Φ.map χ) := by
    have := hq.isStronglyCartesian_homLift f (Φ.map χ)
    infer_instance
  exact Functor.isoClassMk_eq_pullbackFiber_of_isCartesian f
    ((Stacks.RepresentableMorphism.inducedFiberFunctor p q Φ hΦ W).obj a)
    ((Stacks.RepresentableMorphism.inducedFiberFunctor p q Φ hΦ V).obj
      (Functor.pullbackFiber p a f)) (Φ.map χ) hχq hcart

/-- A functor induces a map on isomorphism classes of objects. -/
private def isoClassMapOfFunctor {D : Type objA} [Category.{homA} D] {E : Type objY}
    [Category.{homY} E] (Φ : D ⥤ E) :
    Quotient (isIsomorphicSetoid D) → Quotient (isIsomorphicSetoid E) :=
  Quotient.map Φ.obj fun _ _ hab =>
    (isIsomorphicSetoid_r_iff _ _).2 ⟨Φ.mapIso ((isIsomorphicSetoid_r_iff _ _).1 hab).some⟩

private noncomputable def isoClassPresheafIsoOfMutuallyInverseOnObjects
    {C : Type baseObj} [Category.{baseHom} C]
    {S : Type objA} [Category.{homA} S]
    {T : Type objA} [Category.{homY} T]
    (p : S ⥤ C) (q : T ⥤ C)
    [p.IsFibered] [q.IsFibered]
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
    (Φ : S ⥤ T) (hΦ : Φ ⋙ q = p)
    (Ψ : T ⥤ S) (hΨ : Ψ ⋙ p = q)
    (hΨΦ : ∀ x : S, Ψ.obj (Φ.obj x) = x)
    (hΦΨ : ∀ y : T, Φ.obj (Ψ.obj y) = y) :
    p.isoClassPresheaf ≅ q.isoClassPresheaf := by
  letI : p.IsFibered := hp.isFibered
  letI : q.IsFibered := hq.isFibered
  let φFiber (V : C) : p.Fiber V ⥤ q.Fiber V :=
    Functor.Fiber.inducedFunctor (F := Functor.Fiber.fiberInclusion ⋙ Φ) (by
      rw [Functor.assoc, hΦ]
      exact Functor.Fiber.fiberInclusion_comp_eq_const)
  let ψFiber (V : C) : q.Fiber V ⥤ p.Fiber V :=
    Functor.Fiber.inducedFunctor (F := Functor.Fiber.fiberInclusion ⋙ Ψ) (by
      rw [Functor.assoc, hΨ]
      exact Functor.Fiber.fiberInclusion_comp_eq_const)
  let φClass (V : C) : p.isoClassPresheaf.obj (Opposite.op V) →
      q.isoClassPresheaf.obj (Opposite.op V) :=
    isoClassMapOfFunctor (φFiber V)
  let ψClass (V : C) : q.isoClassPresheaf.obj (Opposite.op V) →
      p.isoClassPresheaf.obj (Opposite.op V) :=
    isoClassMapOfFunctor (ψFiber V)
  have hleft (V : C) (x : p.isoClassPresheaf.obj (Opposite.op V)) :
      ψClass V (φClass V x) = x := by
    induction x using Quotient.ind with
    | _ a =>
      apply Quotient.sound
      apply (Functor.isIsomorphicSetoid_r_iff _ _).2
      exact ⟨eqToIso (Subtype.ext (hΨΦ a.1))⟩
  have hright (V : C) (x : q.isoClassPresheaf.obj (Opposite.op V)) :
      φClass V (ψClass V x) = x := by
    induction x using Quotient.ind with
    | _ a =>
      apply Quotient.sound
      apply (Functor.isIsomorphicSetoid_r_iff _ _).2
      exact ⟨eqToIso (Subtype.ext (hΦΨ a.1))⟩
  have hnat {V W : C} (f : V ⟶ W) (x : p.isoClassPresheaf.obj (Opposite.op W)) :
      φClass V (p.isoClassPresheaf.map f.op x) =
        q.isoClassPresheaf.map f.op (φClass W x) := by
    induction x using Quotient.ind with
    | _ a =>
      change φClass V (p.isoClassPresheaf.map f.op (Functor.isoClassMk p a)) = _
      rw [Functor.isoClassPresheaf_map_isoClassMk]
      exact isoClassMk_inducedFiberFunctor_pullbackFiber p q hq Φ hΦ f a
  exact NatIso.ofComponents (fun V => Equiv.toIso
    { toFun := φClass V.unop
      invFun := ψClass V.unop
      left_inv := hleft V.unop
      right_inv := hright V.unop }) (by
        intro V W f
        ext x
        exact hnat f.unop x)

section BaseChange

universe uC vC uT vT uD vD uA vA uY vY
variable {C : Type uC} [Category.{vC} C] {T : Type uT} [Category.{vT} T]
  {D : Type uD} [Category.{vD} D] {A : Type uA} [Category.{vA} A]
  {Y : Type uY} [Category.{vY} Y]

private def baseChangeFunctor (R : D ⥤ T) (pT : T ⥤ C) (pA : A ⥤ C)
    (pY : Y ⥤ C) (G : T ⥤ Y) (F : A ⥤ Y) :
    TwoFibreProductOver (R ⋙ pT) pA pY (R ⋙ G) F ⥤
      TwoFibreProductOver pT pA pY G F where
  obj P := { P with x := R.obj P.x }
  map φ := { φ with
    a := R.map φ.a
    ha := by
      have := φ.ha
      exact IsHomLift.of_fac' pT φ.hbase (R.map φ.a)
        (IsHomLift.domain_eq (R ⋙ pT) φ.hbase φ.a)
        (IsHomLift.codomain_eq (R ⋙ pT) φ.hbase φ.a)
        (IsHomLift.fac' (R ⋙ pT) φ.hbase φ.a) }
  map_id P := TwoFibreProductOver.Hom.ext' (R.map_id _) rfl
  map_comp φ ψ := TwoFibreProductOver.Hom.ext' (R.map_comp _ _) rfl

private def baseChangeFiberFunctor (R : D ⥤ T) (pT : T ⥤ C) (pA : A ⥤ C)
    (pY : Y ⥤ C) (G : T ⥤ Y) (F : A ⥤ Y) (V : D) :
    (TwoFibreProductOver.fst (R ⋙ pT) pA pY (R ⋙ G) F).Fiber V ⥤
      (TwoFibreProductOver.fst pT pA pY G F).Fiber (R.obj V) where
  obj P := ⟨(baseChangeFunctor R pT pA pY G F).obj P.1, congrArg R.obj P.2⟩
  map {P Q} φ := ⟨(baseChangeFunctor R pT pA pY G F).map φ.1, by
    have := φ.2
    apply IsHomLift.of_fac' (TwoFibreProductOver.fst pT pA pY G F)
      (𝟙 (R.obj V)) ((baseChangeFunctor R pT pA pY G F).map φ.1)
      (congrArg R.obj P.2) (congrArg R.obj Q.2)
    change R.map φ.1.a = _
    have he := IsHomLift.fac' (TwoFibreProductOver.fst (R ⋙ pT) pA pY (R ⋙ G) F) (𝟙 V) φ.1
    change φ.1.a = _ at he
    rw [he]
    rw [Category.id_comp, eqToHom_trans, eqToHom_map, Category.id_comp]
    exact eqToHom_eq_eqToHom_comp_eqToHom (Z := T) _ _ _⟩
  map_id P := Subtype.ext ((baseChangeFunctor R pT pA pY G F).map_id P.1)
  map_comp φ ψ := Subtype.ext ((baseChangeFunctor R pT pA pY G F).map_comp φ.1 ψ.1)

private theorem baseChangeFiberFunctor_obj_surjective
    (R : D ⥤ T) (pT : T ⥤ C) (pA : A ⥤ C)
    (pY : Y ⥤ C) (G : T ⥤ Y) (F : A ⥤ Y) (V : D) :
    Function.Surjective (baseChangeFiberFunctor R pT pA pY G F V).obj := by
  rintro ⟨⟨b, x, y, hx, hy, i, hi⟩, he⟩
  change x = R.obj V at he
  subst x
  exact ⟨⟨⟨b, V, y, hx, hy, i, hi⟩, rfl⟩, rfl⟩

private theorem baseChangeFiberFunctor_full
    (R : D ⥤ T) (pT : T ⥤ C) (pA : A ⥤ C)
    (pY : Y ⥤ C) (G : T ⥤ Y) (F : A ⥤ Y) (V : D) :
    (baseChangeFiberFunctor R pT pA pY G F V).Full := by
  constructor
  rintro ⟨⟨b, x, y, hx, hy, i, hi⟩, he⟩ ⟨⟨b', x', y', hx', hy', i', hi'⟩, he'⟩ φ
  change x = V at he
  change x' = V at he'
  subst x
  subst x'
  have hφ := φ.2
  have ha : φ.1.a = 𝟙 (R.obj V) := by
    have h := IsHomLift.fac' (TwoFibreProductOver.fst pT pA pY G F) (𝟙 (R.obj V)) φ.1
    rw [Category.id_comp, eqToHom_trans] at h
    change φ.1.a = eqToHom (rfl : R.obj V = R.obj V) at h
    exact h.trans (eqToHom_refl _ _)
  let ψ : (⟨b, V, y, hx, hy, i, hi⟩ : TwoFibreProductOver (R ⋙ pT) pA pY (R ⋙ G) F) ⟶
      ⟨b', V, y', hx', hy', i', hi'⟩ :=
    { hbase := φ.1.hbase
      a := 𝟙 V
      b := φ.1.b
      ha := by
        have hh := φ.1.ha
        rw [ha] at hh
        let : pT.IsHomLift φ.1.hbase (𝟙 (R.obj V)) := hh
        apply IsHomLift.of_fac' (R ⋙ pT) φ.1.hbase (𝟙 V) hx hx'
        simpa using IsHomLift.fac' pT φ.1.hbase (𝟙 (R.obj V))
      hb := φ.1.hb
      w := by simpa [ha, baseChangeFiberFunctor, baseChangeFunctor] using φ.1.w }
  refine ⟨⟨ψ, IsHomLift.of_fac' _ (𝟙 V) ψ rfl rfl (by simp [ψ, TwoFibreProductOver.fst])⟩, ?_⟩
  apply Subtype.ext
  apply TwoFibreProductOver.Hom.ext'
  · simpa [baseChangeFiberFunctor, baseChangeFunctor, ψ] using ha.symm
  · rfl

private noncomputable def baseChangeIsoClassPresheafIso
    {D : Type uT} [Category.{vD} D]
    (R : D ⥤ T) (pT : T ⥤ C) (pA : A ⥤ C)
    (pY : Y ⥤ C) (G : T ⥤ Y) (F : A ⥤ Y)
    (hp : (TwoFibreProductOver.fst (R ⋙ pT) pA pY (R ⋙ G) F).IsFiberedInGroupoids)
    (hq : (TwoFibreProductOver.fst pT pA pY G F).IsFiberedInGroupoids) :
    letI := hp.isFibered
    letI := hq.isFibered
    (TwoFibreProductOver.fst (R ⋙ pT) pA pY (R ⋙ G) F).isoClassPresheaf ≅
      R.op ⋙ (TwoFibreProductOver.fst pT pA pY G F).isoClassPresheaf := by
  let p := TwoFibreProductOver.fst (R ⋙ pT) pA pY (R ⋙ G) F
  let q := TwoFibreProductOver.fst pT pA pY G F
  letI := hp.isFibered
  letI := hq.isFibered
  let Φ := baseChangeFunctor R pT pA pY G F
  let ΦV := baseChangeFiberFunctor R pT pA pY G F
  let φ (V : D) : p.isoClassPresheaf.obj (.op V) → q.isoClassPresheaf.obj (.op (R.obj V)) :=
    isoClassMapOfFunctor (ΦV V)
  have hbij (V : D) : Function.Bijective (φ V) := by
    have : (ΦV V).Full := baseChangeFiberFunctor_full R pT pA pY G F V
    have : IsGroupoid (p.Fiber V) := hp.fiber_isGroupoid V
    constructor
    · intro a b hab
      induction a using Quotient.ind with | _ a =>
        induction b using Quotient.ind with | _ b =>
          obtain ⟨i⟩ := (isoClassMk_eq_iff ((ΦV V).obj a) ((ΦV V).obj b)).1 hab
          exact isoClassMk_eq_of_iso (asIso ((ΦV V).preimage i.hom))
    · intro b
      obtain ⟨b, rfl⟩ := isoClassMk_surjective b
      obtain ⟨a, rfl⟩ := baseChangeFiberFunctor_obj_surjective R pT pA pY G F V b
      exact ⟨isoClassMk p a, rfl⟩
  have hnat {V W : D} (g : V ⟶ W) (x : p.isoClassPresheaf.obj (.op W)) :
      φ V (p.isoClassPresheaf.map g.op x) =
        q.isoClassPresheaf.map (R.map g).op (φ W x) := by
    induction x using Quotient.ind with | _ a =>
      change φ V (p.isoClassPresheaf.map g.op (isoClassMk p a)) = _
      rw [isoClassPresheaf_map_isoClassMk]
      change isoClassMk q ((ΦV V).obj (pullbackFiber p a g)) =
        q.isoClassPresheaf.map (R.map g).op (isoClassMk q ((ΦV W).obj a))
      rw [isoClassPresheaf_map_isoClassMk]
      let χ := IsPreFibered.pullbackMap a.2 g
      have hχq : q.IsHomLift (R.map g) (Φ.map χ) := by
        apply IsHomLift.of_fac' q (R.map g) (Φ.map χ)
          (congrArg R.obj (pullbackFiber p a g).2) (congrArg R.obj a.2)
        change R.map χ.a = _
        have he := IsHomLift.fac' p g χ
        change χ.a = _ at he
        rw [he]
        simp only [eqToHom_map, Functor.map_comp]
        rfl
      have hcart : q.IsCartesian (R.map g) (Φ.map χ) := by
        have := hq.isStronglyCartesian_homLift (R.map g) (Φ.map χ)
        infer_instance
      exact isoClassMk_eq_pullbackFiber_of_isCartesian (R.map g)
        ((ΦV W).obj a) ((ΦV V).obj (pullbackFiber p a g)) (Φ.map χ) hχq hcart
  exact NatIso.ofComponents (fun V => (Equiv.ofBijective (φ V.unop) (hbij V.unop)).toIso)
    (by intro V W g; ext x; exact hnat g.unop x)

private noncomputable def baseChangeIsoClassPresheafIsoOfCompEq
    {D : Type uT} [Category.{vD} D]
    (R : D ⥤ T) (pD : D ⥤ C) (pT : T ⥤ C) (pA : A ⥤ C)
    (pY : Y ⥤ C) (G : T ⥤ Y) (F : A ⥤ Y) (hR : R ⋙ pT = pD)
    (hp : (TwoFibreProductOver.fst pD pA pY (R ⋙ G) F).IsFiberedInGroupoids)
    (hq : (TwoFibreProductOver.fst pT pA pY G F).IsFiberedInGroupoids) :
    letI := hp.isFibered
    letI := hq.isFibered
    (TwoFibreProductOver.fst pD pA pY (R ⋙ G) F).isoClassPresheaf ≅
      R.op ⋙ (TwoFibreProductOver.fst pT pA pY G F).isoClassPresheaf := by
  subst pD
  exact baseChangeIsoClassPresheafIso R pT pA pY G F hp hq

end BaseChange

universe u v w

/-- The presheaf of isomorphism classes of pairs `(x, φ : h* y ⟶ f(x))`
on schemes over `U` is an algebraic space, naturally in the test scheme. -/
public def IsAlgebraicSpacePairIsoClassPresheaf
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w}
      (AlgebraicGeometry.BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴)
    (c : 𝒴.val.p.ChoiceOfPullbacks)
    (U : AlgebraicGeometry.BigFppfOver B S hS) (y : 𝒴.val.p.Fiber U) : Prop :=
  let 𝒰 := AlgebraicGeometry.BigFppfOver B U.left.1 U.left.2
  let P := U.iteratedSliceBackward.op ⋙
    PairIsoClass.presheaf (CatFiberedInGroupoids.homFunctor f) c y
      𝒳.2 𝒴.2 (CatFiberedInGroupoids.homFunctor_comp_p f)
  ∃ F : 𝒰ᵒᵖ ⥤ Type u,
    AlgebraicGeometry.IsAlgebraicSpace B U.left.1 U.left.2 F ∧
      ∃ e : ∀ V, P.obj V ≃ F.obj V,
        ∀ ⦃V W⦄ (g : V ⟶ W) (a : P.obj V),
          e W (P.map g a) = F.map g (e V a)

/-- A natural family of equivalences with a presheaf transfers along an isomorphism of
presheaves. -/
private theorem exists_natural_equiv_of_iso {J : Type uAux} [Category.{vAux} J]
    {P Q : Jᵒᵖ ⥤ Type objA} {F : Jᵒᵖ ⥤ Type objD} (i : Q ≅ P) (e : ∀ V, P.obj V ≃ F.obj V)
    (he : ∀ ⦃V W⦄ (g : V ⟶ W) (a : P.obj V), e W (P.map g a) = F.map g (e V a)) :
    ∃ e' : ∀ V, Q.obj V ≃ F.obj V,
      ∀ ⦃V W⦄ (g : V ⟶ W) (a : Q.obj V), e' W (Q.map g a) = F.map g (e' V a) :=
  ⟨fun V => (i.app V).toEquiv.trans (e V), fun V W g a => by
    change e W (i.hom.app W (Q.map g a)) = F.map g (e V (i.hom.app V a))
    exact (congrArg (e W) (congrArg (fun k => k a) (i.hom.naturality g))).trans (he g _)⟩

private theorem sliceFunctor_comp_p
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (AlgebraicGeometry.BigFppfOver B S hS)}
    (c : 𝒴.val.p.ChoiceOfPullbacks) (U : AlgebraicGeometry.BigFppfOver B S hS)
    (y : 𝒴.val.p.Fiber U) :
    (U.iteratedSliceBackward ⋙ c.sliceFunctor y) ⋙ 𝒴.val.p = Over.map U.hom := by
  rw [Functor.assoc, c.sliceFunctor_comp y, Over.iteratedSliceBackward_forget]

private theorem fst_overMap_isFiberedInGroupoids
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w}
      (AlgebraicGeometry.BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴)
    (U : AlgebraicGeometry.BigFppfOver B S hS)
    (G : AlgebraicGeometry.BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
    (hG : G ⋙ 𝒴.val.p = Over.map U.hom) :
    (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p G
      (CatFiberedInGroupoids.homFunctor f)).IsFiberedInGroupoids :=
  Stack.fst_isFiberedInGroupoids_overMap
    (𝒞 := AlgebraicGeometry.BigFppfSite.Schemes B) (U := U.left) (S := B.obj hS)
    (f := U.hom) (𝒜 := 𝒳.val.obj) (𝒟 := 𝒴.val.obj)
    𝒳.val.p 𝒴.val.p G (CatFiberedInGroupoids.homFunctor f)
    𝒳.isFiberedInGroupoids 𝒴.isFiberedInGroupoids hG
    (CatFiberedInGroupoids.homFunctor_comp_p f)

/-- A morphism of categories fibred in groupoids that is representable by algebraic spaces is
faithful on every fibre. -/
private theorem inducedFiberFunctor_faithful_of_isRepresentableByAlgebraicSpaces
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w}
      (AlgebraicGeometry.BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴)
    (c : 𝒴.val.p.ChoiceOfPullbacks)
    (hrep : AlgebraicGeometry.IsRepresentableByAlgebraicSpaces B S hS f.hom)
    (U : AlgebraicGeometry.BigFppfOver B S hS) :
    (Stacks.RepresentableMorphism.inducedFiberFunctor 𝒳.val.p 𝒴.val.p
      (CatFiberedInGroupoids.homFunctor f)
      (CatFiberedInGroupoids.homFunctor_comp_p f) U).Faithful := by
  constructor
  intro a b φ φ' h
  have hφ : (CatFiberedInGroupoids.homFunctor f).map (Fiber.fiberInclusion.map φ) =
      (CatFiberedInGroupoids.homFunctor f).map (Fiber.fiberInclusion.map φ') :=
    (Stacks.RepresentableMorphism.inducedFiberFunctor_map_eq_iff
      𝒳.val.p 𝒴.val.p (CatFiberedInGroupoids.homFunctor f)
      (CatFiberedInGroupoids.homFunctor_comp_p f) U φ φ').1 h
  let 𝒰 := AlgebraicGeometry.BigFppfOver B U.left.1 U.left.2
  let p𝒰 : 𝒰 ⥤ AlgebraicGeometry.BigFppfOver B S hS := Over.map U.hom
  let y : 𝒴.val.p.Fiber U :=
    ⟨(CatFiberedInGroupoids.homFunctor f).obj (Fiber.fiberInclusion.obj b),
      (Functor.congr_obj (CatFiberedInGroupoids.homFunctor_comp_p f)
        (Fiber.fiberInclusion.obj b)).trans b.2⟩
  let G : 𝒰 ⥤ 𝒴.val.obj := U.iteratedSliceBackward ⋙ c.sliceFunctor y
  have hG : G ⋙ 𝒴.val.p = p𝒰 := sliceFunctor_comp_p B S hS c U y
  obtain ⟨Fspace, hspace, hEquiv⟩ := hrep U G hG
  let Pcat : CatFiberedInGroupoids 𝒰 :=
    ⟨BasedCategory.ofFunctor (TwoFibreProductOver.fst p𝒰 𝒳.val.p 𝒴.val.p G
      (CatFiberedInGroupoids.homFunctor f)), fst_overMap_isFiberedInGroupoids B S hS f U G hG⟩
  have hsetoid := (AlgebraicGeometry.isRepresentableByAlgebraicSpace_iff
    B U.left.1 U.left.2 Pcat).mp ⟨Fspace, hspace, hEquiv⟩ |>.1
  let v₀ : 𝒰 := Over.mk (𝟙 U.left)
  have hv₀ : p𝒰.obj v₀ = U := rfl
  have hid : (Over.homMk (𝟙 U.left) : U ⟶ U) = 𝟙 U := by
    ext
    rfl
  have hGv : G.obj v₀ = Fiber.fiberInclusion.obj (c.obj (𝟙 U) y) :=
    congrArg (fun m : U ⟶ U => Fiber.fiberInclusion.obj (c.obj m y)) hid
  let ξ : G.obj v₀ ≅ (CatFiberedInGroupoids.homFunctor f).obj
      (Fiber.fiberInclusion.obj b) :=
    eqToIso hGv ≪≫ Fiber.fiberInclusion.mapIso (c.objIdIso y)
  have hξ : 𝒴.val.p.IsHomLift (𝟙 U) ξ.hom := by
    have hobj : 𝒴.val.p.obj (G.obj v₀) = U :=
      (Functor.congr_obj hG v₀).trans hv₀
    have h1 : 𝒴.val.p.IsHomLift (𝟙 U) (eqToHom hGv) := by
      apply IsHomLift.of_fac' 𝒴.val.p (𝟙 U) (eqToHom hGv) hobj
        (c.obj (𝟙 U) y).2
      rw [Category.id_comp, eqToHom_trans, eqToHom_map]
    let : 𝒴.val.p.IsHomLift (𝟙 U)
        (Fiber.fiberInclusion.map (c.objIdIso y).hom) := (c.objIdIso y).hom.2
    change 𝒴.val.p.IsHomLift (𝟙 U)
      (eqToHom hGv ≫ Fiber.fiberInclusion.map (c.objIdIso y).hom)
    exact IsHomLift.comp_of_lift_id 𝒴.val.p U _ _
  exact fiberHom_injective_of_fst_isFiberedInSetoids
    p𝒰 𝒳.val.p 𝒴.val.p G (CatFiberedInGroupoids.homFunctor f)
    (CatFiberedInGroupoids.homFunctor_comp_p f) 𝒳.isFiberedInGroupoids
    hsetoid U v₀ hv₀ ξ hξ φ φ' hφ

/-- For a morphism of categories fibred in groupoids that is representable by algebraic spaces,
the presheaf of isomorphism classes of pairs attached to any object of the target is an
algebraic space. -/
private theorem isAlgebraicSpacePairIsoClassPresheaf_of_isRepresentableByAlgebraicSpaces
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w}
      (AlgebraicGeometry.BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴)
    (c : 𝒴.val.p.ChoiceOfPullbacks)
    (hrep : AlgebraicGeometry.IsRepresentableByAlgebraicSpaces B S hS f.hom)
    (U : AlgebraicGeometry.BigFppfOver B S hS) (y : 𝒴.val.p.Fiber U) :
    IsAlgebraicSpacePairIsoClassPresheaf B S hS f c U y := by
  let 𝒰 := AlgebraicGeometry.BigFppfOver B U.left.1 U.left.2
  let p𝒰 : 𝒰 ⥤ AlgebraicGeometry.BigFppfOver B S hS := Over.map U.hom
  let G : 𝒰 ⥤ 𝒴.val.obj := U.iteratedSliceBackward ⋙ c.sliceFunctor y
  have hG : G ⋙ 𝒴.val.p = p𝒰 := sliceFunctor_comp_p B S hS c U y
  obtain ⟨Fspace, hspace, hEquiv⟩ := hrep U G hG
  let Fst := TwoFibreProductOver.fst p𝒰 𝒳.val.p 𝒴.val.p G
    (CatFiberedInGroupoids.homFunctor f)
  have hFst : Fst.IsFiberedInGroupoids := fst_overMap_isFiberedInGroupoids B S hS f U G hG
  let Pcat : CatFiberedInGroupoids 𝒰 := ⟨BasedCategory.ofFunctor Fst, hFst⟩
  have hclass := (AlgebraicGeometry.isRepresentableByAlgebraicSpace_iff
    B U.left.1 U.left.2 Pcat).mp ⟨Fspace, hspace, hEquiv⟩ |>.2
  let := hFst.isFibered
  let i : Fst.isoClassPresheaf ≅ U.iteratedSliceBackward.op ⋙
      PairIsoClass.presheaf (CatFiberedInGroupoids.homFunctor f) c y
        𝒳.2 𝒴.2 (CatFiberedInGroupoids.homFunctor_comp_p f) :=
    baseChangeIsoClassPresheafIsoOfCompEq U.iteratedSliceBackward p𝒰 (Over.forget U)
      𝒳.val.p 𝒴.val.p (c.sliceFunctor y) (CatFiberedInGroupoids.homFunctor f)
      (Over.iteratedSliceBackward_forget U) hFst
      (PairIsoClass.isFiberedInGroupoids _ c y 𝒳.2 𝒴.2
        (CatFiberedInGroupoids.homFunctor_comp_p f))
  obtain ⟨Fcls, hcls, e, he⟩ := hclass
  exact ⟨Fcls, hcls, exists_natural_equiv_of_iso i.symm e he⟩

private theorem exists_iso_sliceFunctor_isHomLift
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (AlgebraicGeometry.BigFppfOver B S hS)}
    (c : 𝒴.val.p.ChoiceOfPullbacks) (U : AlgebraicGeometry.BigFppfOver B S hS)
    (G : AlgebraicGeometry.BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
    (hG : G ⋙ 𝒴.val.p = Over.map U.hom)
    (hG' : (U.iteratedSliceEquiv.functor ⋙ G) ⋙ 𝒴.val.p = Over.forget U) :
    ∃ α : G ≅ U.iteratedSliceBackward ⋙ c.sliceFunctor
        (Functor.ChoiceOfPullbacks.sliceObj (U.iteratedSliceEquiv.functor ⋙ G) hG'),
      ∀ V, 𝒴.val.p.IsHomLift (𝟙 ((Over.map U.hom).obj V)) (α.hom.app V) := by
  let p𝒰 : AlgebraicGeometry.BigFppfOver B U.left.1 U.left.2 ⥤
      AlgebraicGeometry.BigFppfOver B S hS := Over.map U.hom
  replace hG : G ⋙ 𝒴.val.p = p𝒰 := hG
  let G' := U.iteratedSliceEquiv.functor ⋙ G
  let α' := c.sliceFunctorIso G' hG' 𝒴.isFiberedInGroupoids
  let α : G ≅ U.iteratedSliceBackward ⋙
      c.sliceFunctor (Functor.ChoiceOfPullbacks.sliceObj G' hG') :=
    (Functor.leftUnitor G).symm ≪≫
      Functor.isoWhiskerRight U.iteratedSliceEquiv.counitIso G ≪≫
      Functor.associator U.iteratedSliceEquiv.inverse U.iteratedSliceEquiv.functor G ≪≫
      Functor.isoWhiskerLeft U.iteratedSliceEquiv.inverse α'
  refine ⟨α, fun V => ?_⟩
  have hc : p𝒰.map (U.iteratedSliceEquiv.counitIso.app V).hom = 𝟙 (p𝒰.obj V) := by
    ext
    rfl
  have hmap : 𝒴.val.p.IsHomLift (𝟙 (p𝒰.obj V))
      (G.map (U.iteratedSliceEquiv.counitIso.app V).hom) := by
    have hunit : p𝒰.IsHomLift (𝟙 (p𝒰.obj V))
        (U.iteratedSliceEquiv.counitIso.app V).hom := by
      apply IsHomLift.of_fac' p𝒰 (𝟙 (p𝒰.obj V)) _ rfl rfl
      simpa [hc]
    let : p𝒰.IsHomLift (𝟙 (p𝒰.obj V))
        (U.iteratedSliceEquiv.counitIso.app V).hom := hunit
    have hh := Functor.isHomLift_map_of_comp_eq hG (𝟙 (p𝒰.obj V))
      (U.iteratedSliceEquiv.counitIso.app V).hom
    simpa [hc] using hh
  have hα' := c.sliceFunctorIso_hom_app_isHomLift G' hG' 𝒴.isFiberedInGroupoids
    (U.iteratedSliceEquiv.inverse.obj V)
  have hbase : (U.iteratedSliceEquiv.inverse.obj V).left = p𝒰.obj V := by
    rfl
  rw [hbase] at hα'
  have hmorph : α.hom.app V =
      G.map (U.iteratedSliceEquiv.counitIso.app V).hom ≫
        (c.sliceFunctorIso G' hG' 𝒴.isFiberedInGroupoids).hom.app
          (U.iteratedSliceEquiv.inverse.obj V) := by
    have h0 : α.hom.app V =
        𝟙 (G.obj V) ≫ G.map (U.iteratedSliceEquiv.counitIso.app V).hom ≫
          𝟙 _ ≫ (c.sliceFunctorIso G' hG' 𝒴.isFiberedInGroupoids).hom.app
            (U.iteratedSliceEquiv.inverse.obj V) := rfl
    rw [h0, Category.id_comp]
    exact congrArg (fun m => G.map (U.iteratedSliceEquiv.counitIso.app V).hom ≫ m)
      (Category.id_comp _)
  rw [hmorph]
  exact @IsHomLift.comp_of_lift_id _ _ _ _ 𝒴.val.p (p𝒰.obj V) _ _ _
    (G.map (U.iteratedSliceEquiv.counitIso.app V).hom)
    ((c.sliceFunctorIso G' hG' 𝒴.isFiberedInGroupoids).hom.app
      (U.iteratedSliceEquiv.inverse.obj V)) hmap hα'

private theorem isRepresentableByAlgebraicSpace_fst_of_isHomLift_iso
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w}
      (AlgebraicGeometry.BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴)
    (c : 𝒴.val.p.ChoiceOfPullbacks)
    (hfaithful : ∀ U : AlgebraicGeometry.BigFppfOver B S hS,
      (Stacks.RepresentableMorphism.inducedFiberFunctor 𝒳.val.p 𝒴.val.p
        (CatFiberedInGroupoids.homFunctor f)
        (CatFiberedInGroupoids.homFunctor_comp_p f) U).Faithful)
    (U : AlgebraicGeometry.BigFppfOver B S hS) (y : 𝒴.val.p.Fiber U)
    (hy : IsAlgebraicSpacePairIsoClassPresheaf B S hS f c U y)
    (G : AlgebraicGeometry.BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
    (hG : G ⋙ 𝒴.val.p = Over.map U.hom)
    (α : G ≅ U.iteratedSliceBackward ⋙ c.sliceFunctor y)
    (hα : ∀ V, 𝒴.val.p.IsHomLift (𝟙 ((Over.map U.hom).obj V)) (α.hom.app V)) :
    AlgebraicGeometry.IsRepresentableByAlgebraicSpace B U.left.1 U.left.2
      ⟨BasedCategory.ofFunctor (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p G
        (CatFiberedInGroupoids.homFunctor f)),
        fst_overMap_isFiberedInGroupoids B S hS f U G hG⟩ := by
  let 𝒰 := AlgebraicGeometry.BigFppfOver B U.left.1 U.left.2
  let p𝒰 : 𝒰 ⥤ AlgebraicGeometry.BigFppfOver B S hS := Over.map U.hom
  let F := CatFiberedInGroupoids.homFunctor f
  let Gcan : 𝒰 ⥤ 𝒴.val.obj := U.iteratedSliceBackward ⋙ c.sliceFunctor y
  let Fst : TwoFibreProductOver p𝒰 𝒳.val.p 𝒴.val.p G F ⥤ 𝒰 :=
    TwoFibreProductOver.fst p𝒰 𝒳.val.p 𝒴.val.p G F
  have hFst : Fst.IsFiberedInGroupoids := fst_overMap_isFiberedInGroupoids B S hS f U G hG
  let FstCan : TwoFibreProductOver p𝒰 𝒳.val.p 𝒴.val.p Gcan F ⥤ 𝒰 :=
    TwoFibreProductOver.fst p𝒰 𝒳.val.p 𝒴.val.p Gcan F
  have hFstCan : FstCan.IsFiberedInGroupoids :=
    fst_overMap_isFiberedInGroupoids B S hS f U Gcan (sliceFunctor_comp_p B S hS c U y)
  have hsetoid : Fst.IsFiberedInSetoids := fst_isFiberedInSetoids_of_faithful
    p𝒰 𝒳.val.p 𝒴.val.p G F (CatFiberedInGroupoids.homFunctor_comp_p f) hFst hfaithful
  let Pcat : CatFiberedInGroupoids 𝒰 := ⟨BasedCategory.ofFunctor Fst, hFst⟩
  obtain ⟨Fspace, hspace, e, he⟩ := hy
  let : Fst.IsFibered := hFst.isFibered
  let : FstCan.IsFibered := hFstCan.isFibered
  have hiso := isoClassPresheafIsoOfMutuallyInverseOnObjects
    Fst FstCan hFst hFstCan
    (TwoFibreProductOver.reindex α hα)
    (TwoFibreProductOver.reindex_comp_fst α hα)
    (TwoFibreProductOver.reindexSymm α hα)
    (TwoFibreProductOver.reindexSymm_comp_fst α hα)
    (TwoFibreProductOver.reindexSymm_reindex_obj α hα)
    (TwoFibreProductOver.reindex_reindexSymm_obj α hα)
  let i : FstCan.isoClassPresheaf ≅ U.iteratedSliceBackward.op ⋙
      PairIsoClass.presheaf F c y 𝒳.2 𝒴.2 (CatFiberedInGroupoids.homFunctor_comp_p f) :=
    baseChangeIsoClassPresheafIsoOfCompEq U.iteratedSliceBackward p𝒰 (Over.forget U)
      𝒳.val.p 𝒴.val.p (c.sliceFunctor y) F (Over.iteratedSliceBackward_forget U) hFstCan
      (PairIsoClass.isFiberedInGroupoids _ c y 𝒳.2 𝒴.2
        (CatFiberedInGroupoids.homFunctor_comp_p f))
  let j := hiso ≪≫ i
  have hclassActual : AlgebraicGeometry.IsAlgebraicSpaceIsoClassPresheaf
      B U.left.1 U.left.2 Pcat := by
    exact ⟨Fspace, hspace, exists_natural_equiv_of_iso j e he⟩
  exact (AlgebraicGeometry.isRepresentableByAlgebraicSpace_iff
    B U.left.1 U.left.2 Pcat).mpr ⟨hsetoid, hclassActual⟩

/-- **Stacks 02ZY.** A morphism of categories fibred in groupoids is representable by
algebraic spaces if and only if its functors on fibres are faithful and, for every
object of the target over a scheme, the associated presheaf of pairs is an
algebraic space over that scheme. -/
@[stacks 02ZY]
public theorem isRepresentableByAlgebraicSpaces_iff_associatedMap
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w}
      (AlgebraicGeometry.BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴)
    (c : 𝒴.val.p.ChoiceOfPullbacks) :
    AlgebraicGeometry.IsRepresentableByAlgebraicSpaces B S hS f.hom ↔
      ((∀ U : AlgebraicGeometry.BigFppfOver B S hS,
        (Stacks.RepresentableMorphism.inducedFiberFunctor 𝒳.val.p 𝒴.val.p
          (CatFiberedInGroupoids.homFunctor f)
          (CatFiberedInGroupoids.homFunctor_comp_p f) U).Faithful) ∧
        (∀ (U : AlgebraicGeometry.BigFppfOver B S hS) (y : 𝒴.val.p.Fiber U),
          IsAlgebraicSpacePairIsoClassPresheaf B S hS f c U y)) := by
  constructor
  · intro hrep
    exact ⟨inducedFiberFunctor_faithful_of_isRepresentableByAlgebraicSpaces B S hS f c hrep,
      isAlgebraicSpacePairIsoClassPresheaf_of_isRepresentableByAlgebraicSpaces B S hS f c hrep⟩
  · intro h U 𝒰 p𝒰 G hG
    let G' := U.iteratedSliceEquiv.functor ⋙ G
    have hG' : G' ⋙ 𝒴.val.p = Over.forget U := by
      dsimp [G']
      rw [Functor.assoc, hG]
      exact map_eq_forget_iteratedSlice U.hom
    let y := Functor.ChoiceOfPullbacks.sliceObj G' hG'
    obtain ⟨α, hα⟩ := exists_iso_sliceFunctor_isHomLift B S hS c U G hG hG'
    obtain ⟨Fspace, hspace, hEquiv⟩ := isRepresentableByAlgebraicSpace_fst_of_isHomLift_iso
      B S hS f c h.1 U y (h.2 U y) G hG α hα
    exact ⟨Fspace, hspace, hEquiv⟩

end AlgebraicGeometry

end
