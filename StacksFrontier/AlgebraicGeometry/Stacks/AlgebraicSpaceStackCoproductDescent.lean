module

public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStackOneMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafCoproduct
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteCoproduct
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteProperties

/-!
# 1-morphisms out of the algebraic space of a disjoint union

Let `V = ∐ V_l` be a coproduct in the big fppf site of `S`. A family of 1-morphisms `F_l` from the
algebraic spaces `V_l` to an algebraic stack glues to a 1-morphism out of `V`: the pointwise
gluing data are identities on points of one and the same summand, and points with the same image
in two different summands lie over the empty scheme, over which the fibre of a stack is
contractible.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.existsUnique_hom_of_isEmpty`: the fibre of an algebraic
  stack over an empty scheme is contractible.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory

universe u v w

namespace AlgebraicGeometry.Stack

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The fibre of an algebraic stack over an empty scheme is contractible**: between any two
objects over an empty object of the site there is exactly one morphism over the identity. The
empty sieve covers such an object, so this is the sheaf property of morphisms for the empty
covering. -/
theorem AlgebraicStacks.existsUnique_hom_of_isEmpty (𝒴 : AlgebraicStacks.{u, w} B S hS)
    {V : BigFppfOver B S hS} (hV : IsEmpty ((BigFppfOver.toScheme B S hS).obj V))
    {a b : 𝒴.val.val.obj} (ha : 𝒴.val.val.p.obj a = V) (hb : 𝒴.val.val.p.obj b = V) :
    ∃! φ : a ⟶ b, 𝒴.val.val.p.IsHomLift (𝟙 V) φ := by
  have hp : 𝒴.val.val.p.IsStackInGroupoids.{0} (BigFppfOver.topology B S hS) :=
    AlgebraicStacks.isStackInGroupoids 𝒴
  have hcov : Sieve.ofArrows (fun k : PEmpty.{1} => (k.elim : BigFppfOver B S hS))
      (fun k => k.elim) ∈ BigFppfOver.topology B S hS V :=
    (BigFppfOver.topology B S hS).superset_covering bot_le
      (BigFppfOver.bot_mem_topology V hV)
  have h₁ : ∀ k : PEmpty.{1}, 𝒴.val.val.p.IsHomLift
      ((fun k : PEmpty.{1} => (k.elim : (k.elim : BigFppfOver B S hS) ⟶ V)) k)
      ((fun k : PEmpty.{1} => (k.elim : (k.elim : 𝒴.val.val.obj) ⟶ a)) k) := fun k => k.elim
  have h₂ : ∀ k : PEmpty.{1}, 𝒴.val.val.p.IsHomLift
      ((fun k : PEmpty.{1} => (k.elim : (k.elim : BigFppfOver B S hS) ⟶ V)) k ≫ 𝟙 V)
      ((fun k : PEmpty.{1} => (k.elim : (k.elim : 𝒴.val.val.obj) ⟶ b)) k) := fun k => k.elim
  obtain ⟨ζ, ⟨hζ, -⟩, huniq⟩ := hp.existsUnique_hom_of_cover
    (fun k : PEmpty.{1} => (k.elim : (k.elim : BigFppfOver B S hS) ⟶ V)) hcov
    (V₂ := fun k _ => k.elim) (fun k _ => k.elim) (fun k _ => k.elim) (fun k _ => k.elim) (𝟙 V)
    ha (fun k : PEmpty.{1} => (k.elim : (k.elim : 𝒴.val.val.obj) ⟶ a)) hb
    (fun k : PEmpty.{1} => (k.elim : (k.elim : 𝒴.val.val.obj) ⟶ b)) (fun k => k.elim)
  exact ⟨ζ, hζ, fun ζ' hζ' => huniq ζ' ⟨hζ', fun k => k.elim⟩⟩

/-- **Morphisms out of an object over an empty scheme are unique**: two morphisms of an
algebraic stack lying over one and the same `g : W ⟶ V` with `W` empty are equal. The first one
is cartesian, so the second factors through it by a morphism over the identity of `W`, which is
the identity by `AlgebraicGeometry.Stack.AlgebraicStacks.existsUnique_hom_of_isEmpty`. -/
theorem AlgebraicStacks.hom_eq_of_isEmpty (𝒴 : AlgebraicStacks.{u, w} B S hS)
    {W V : BigFppfOver B S hS} (hW : IsEmpty ((BigFppfOver.toScheme B S hS).obj W))
    (g : W ⟶ V) {x y : 𝒴.val.val.obj} (φ φ' : x ⟶ y) [𝒴.val.val.p.IsHomLift g φ]
    [𝒴.val.val.p.IsHomLift g φ'] : φ = φ' := by
  have hg : 𝒴.val.val.p.IsFiberedInGroupoids := 𝒴.val.2
  have := hg.isStronglyCartesian_homLift g φ
  have hx : 𝒴.val.val.p.obj x = W := IsHomLift.domain_eq _ g φ
  have hτ := (existsUnique_hom_of_isEmpty 𝒴 hW hx hx).unique
    (Functor.IsStronglyCartesian.map_isHomLift (p := 𝒴.val.val.p) g φ (f' := g) (g := 𝟙 W)
      (by simp) φ') (IsHomLift.id hx)
  rw [← Functor.IsStronglyCartesian.fac (p := 𝒴.val.val.p) g φ (f' := g) (g := 𝟙 W) (by simp)
    φ', hτ, Category.id_comp]

section Disjoint

variable {𝒴 : AlgebraicStacks.{u, w} B S hS} {T : AlgebraicSpaces B S hS} {K : Type v}
  {T' : K → AlgebraicSpaces B S hS} (e : ∀ k, T' k ⟶ T)
  (hinj : ∀ (k : K) (V : BigFppfOver B S hS) (a a' : (T' k).obj.obj (Opposite.op V)),
    (e k).hom.app _ a = (e k).hom.app _ a' → a = a')
  (hdisj : ∀ (k l : K), k ≠ l → ∀ (V : BigFppfOver B S hS) (a : (T' k).obj.obj (Opposite.op V))
    (b : (T' l).obj.obj (Opposite.op V)), (e k).hom.app _ a = (e l).hom.app _ b →
      IsEmpty ((BigFppfOver.toScheme B S hS).obj V))
  (F : ∀ k, (algebraicSpaceStackFunctor.{u, w} B S hS).obj (T' k) ⟶ 𝒴)

open Classical in
/-- The identification of the pointwise gluing data of a disjoint family: the transport along the
equal points of one summand, and the unique morphism over an empty scheme otherwise. -/
def disjointPhi (k l : K) (V : BigFppfOver B S hS) (a : (T' k).obj.obj (Opposite.op V))
    (b : (T' l).obj.obj (Opposite.op V)) (h : (e k).hom.app _ a = (e l).hom.app _ b) :
    (F k).hom.hom.obj (elt.{u, w} (T' k) V a) ⟶ (F l).hom.hom.obj (elt.{u, w} (T' l) V b) :=
  if hkl : k = l then by
    subst hkl
    exact eqToHom (congrArg (fun z => (F k).hom.hom.obj (elt.{u, w} (T' k) V z))
      (hinj k V a b h))
  else (AlgebraicStacks.existsUnique_hom_of_isEmpty 𝒴 (hdisj k l hkl V a b h)
    (BasedFunctor.w_obj (F k).hom.hom _) (BasedFunctor.w_obj (F l).hom.hom _)).exists.choose

/-- On a single summand, `disjointPhi` is the `eqToHom` along the equality of points given by
injectivity of `e k`. -/
theorem disjointPhi_self (k : K) (V : BigFppfOver B S hS) (a b : (T' k).obj.obj (Opposite.op V))
    (h : (e k).hom.app _ a = (e k).hom.app _ b) :
    disjointPhi e hinj hdisj F k k V a b h = eqToHom (congrArg
      (fun z => (F k).hom.hom.obj (elt.{u, w} (T' k) V z)) (hinj k V a b h)) := by
  rw [disjointPhi, dite_eq_left rfl]

/-- Each morphism `disjointPhi e hinj hdisj F k l V a b h` lies over the identity of `V`. -/
theorem isHomLift_disjointPhi (k l : K) (V : BigFppfOver B S hS)
    (a : (T' k).obj.obj (Opposite.op V)) (b : (T' l).obj.obj (Opposite.op V))
    (h : (e k).hom.app _ a = (e l).hom.app _ b) :
    𝒴.val.val.p.IsHomLift (𝟙 V) (disjointPhi e hinj hdisj F k l V a b h) := by
  by_cases hkl : k = l
  · subst hkl
    rw [disjointPhi_self]
    exact IsHomLift.eqToHom_domain_lift_id _ (BasedFunctor.w_obj (F k).hom.hom _)
  · rw [disjointPhi, dite_eq_right hkl]
    exact (AlgebraicStacks.existsUnique_hom_of_isEmpty 𝒴 (hdisj k l hkl V a b h)
      (BasedFunctor.w_obj (F k).hom.hom _)
      (BasedFunctor.w_obj (F l).hom.hom _)).exists.choose_spec

/-- **Pointwise gluing data for a disjoint family.** -/
def disjointGluing : PointwiseGluing e F where
  φ := disjointPhi e hinj hdisj F
  isHomLift := isHomLift_disjointPhi e hinj hdisj F
  naturality := fun k l {V W} {a a' b b'} κa κb hκ h h' => by
    by_cases hW : IsEmpty ((BigFppfOver.toScheme B S hS).obj W)
    · have hκa : ((algebraicSpaceStackFunctor.{u, w} B S hS).obj (T' k)).val.val.p.IsHomLift
          κa.base κa := IsHomLift.map _ κa
      have hκb : ((algebraicSpaceStackFunctor.{u, w} B S hS).obj (T' l)).val.val.p.IsHomLift
          κa.base κb := by
        rw [hκ]
        exact IsHomLift.map _ κb
      have hFa := BasedFunctor.preserves_isHomLift (F k).hom.hom κa.base κa
      have hFb := BasedFunctor.preserves_isHomLift (F l).hom.hom κa.base κb
      have h₁ := isHomLift_disjointPhi e hinj hdisj F k l V a b h
      have h₂ := isHomLift_disjointPhi e hinj hdisj F k l W a' b' h'
      have l₁ : 𝒴.val.val.p.IsHomLift κa.base
          ((F k).hom.hom.map κa ≫ disjointPhi e hinj hdisj F k l V a b h) :=
        IsHomLift.comp_lift_id_right (p := 𝒴.val.val.p) κa.base ((F k).hom.hom.map κa)
          (disjointPhi e hinj hdisj F k l V a b h)
      have l₂ : 𝒴.val.val.p.IsHomLift κa.base
          (disjointPhi e hinj hdisj F k l W a' b' h' ≫ (F l).hom.hom.map κb) :=
        IsHomLift.comp_lift_id_left (p := 𝒴.val.val.p) κa.base ((F l).hom.hom.map κb)
          (disjointPhi e hinj hdisj F k l W a' b' h')
      exact AlgebraicStacks.hom_eq_of_isEmpty 𝒴 hW κa.base _ _
    · have hV : ¬ IsEmpty ((BigFppfOver.toScheme B S hS).obj V) := fun hV =>
        hW ⟨fun w => hV.false (((BigFppfOver.toScheme B S hS).map κa.base) w)⟩
      obtain rfl : k = l := Classical.byContradiction fun hne => hV (hdisj k l hne V a b h)
      obtain rfl := hinj k V a b h
      obtain rfl := hinj k W a' b' h'
      obtain rfl : κa = κb := elt_hom_ext hκ
      simp [disjointPhi_self]
  cocycle := fun k l m V a b c h₁ h₂ => by
    by_cases hV : IsEmpty ((BigFppfOver.toScheme B S hS).obj V)
    · have i₁ := isHomLift_disjointPhi e hinj hdisj F k l V a b h₁
      have i₂ := isHomLift_disjointPhi e hinj hdisj F l m V b c h₂
      have i₃ := isHomLift_disjointPhi e hinj hdisj F k m V a c (h₁.trans h₂)
      have l₁ : 𝒴.val.val.p.IsHomLift (𝟙 V)
          (disjointPhi e hinj hdisj F k l V a b h₁ ≫ disjointPhi e hinj hdisj F l m V b c h₂) :=
        @IsHomLift.comp_of_lift_id _ _ _ _ _ V _ _ _ _ _ i₁ i₂
      exact AlgebraicStacks.hom_eq_of_isEmpty 𝒴 hV (𝟙 V) _ _
    · obtain rfl : k = l := Classical.byContradiction fun hne => hV (hdisj k l hne V a b h₁)
      obtain rfl : k = m := Classical.byContradiction fun hne => hV (hdisj k m hne V b c h₂)
      obtain rfl := hinj k V a b h₁
      obtain rfl := hinj k V a c h₂
      simp only [disjointPhi_self, eqToHom_trans]

end Disjoint

end AlgebraicGeometry.Stack
