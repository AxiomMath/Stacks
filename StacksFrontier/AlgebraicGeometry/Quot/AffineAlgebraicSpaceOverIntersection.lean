module

public import StacksFrontier.AlgebraicGeometry.Quot.AffineAlgebraicSpaceOverCofilteredLimit

/-!
# Intersections of equalizers of algebraic spaces affine over an affine scheme

Let `T` be an affine scheme of the site and `L` a functor on the test schemes over `T` which is an
algebraic space affine over `T`.  Suppose that for every finite subset `𝒮` of an index set we are
given two morphisms `α_𝒮, z_𝒮 : L ⟶ Q_𝒮` to a functor which is an algebraic space affine over `T`,
whose equalizers shrink as `𝒮` grows.  Then a subfunctor of `L` which is the intersection of all
these equalizers is an algebraic space affine over `T`: it is the cofiltered limit of the
equalizers, which have injective transition maps.

## Main results

* `AlgebraicGeometry.Space.isAffineAlgebraicSpaceOver_of_injective_of_forall_eq`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Intersection

variable {T : BigFppfOver B S hS} (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
  {L R : (SchemesOver ((schemeSpaceFunctor B S hS).obj T))ᵒᵖ ⥤ Type (u + 1)}
  {ι : Type u} (Q : Finset ι → ((SchemesOver ((schemeSpaceFunctor B S hS).obj T))ᵒᵖ ⥤ Type (u + 1)))
  (α z : ∀ 𝒮, L ⟶ Q 𝒮)
  (hmono : ∀ {𝒮 𝒮' : Finset ι}, 𝒮 ⊆ 𝒮' → ∀ X (y : L.obj X),
    (α 𝒮').app X y = (z 𝒮').app X y → (α 𝒮).app X y = (z 𝒮).app X y)

/-- The equalizers of the pairs `α_𝒮, z_𝒮`, as a system indexed by the opposite of the finite
subsets, with the inclusions as transition maps. -/
def equalizerSystem : (Finset ι)ᵒᵖ ⥤
    ((SchemesOver ((schemeSpaceFunctor B S hS).obj T))ᵒᵖ ⥤ Type (u + 1)) where
  obj 𝒮 := equalizer (α 𝒮.unop) (z 𝒮.unop)
  map {𝒮 𝒮'} f := equalizer.lift (equalizer.ι (α 𝒮.unop) (z 𝒮.unop)) (by
    ext X y
    have h := congrArg (fun k => k.app X y) (equalizer.condition (α 𝒮.unop) (z 𝒮.unop))
    exact hmono (leOfHom f.unop) X _ h)
  map_id 𝒮 := equalizer.hom_ext (by simp)
  map_comp f g := equalizer.hom_ext (by simp)

/-- The transition maps of `equalizerSystem` commute with the equalizer inclusions into `L`. -/
theorem equalizerSystem_map_ι {𝒮 𝒮' : (Finset ι)ᵒᵖ} (f : 𝒮 ⟶ 𝒮') :
    (equalizerSystem B S hS Q α z hmono).map f ≫ equalizer.ι (α 𝒮'.unop) (z 𝒮'.unop) =
      equalizer.ι (α 𝒮.unop) (z 𝒮.unop) :=
  equalizer.lift_ι _ _

/-- The equalizer inclusion is injective at every test scheme. -/
theorem injective_equalizer_ι_app (𝒮 : Finset ι) (X : (SchemesOver
    ((schemeSpaceFunctor B S hS).obj T))ᵒᵖ) :
    Function.Injective ((equalizer.ι (α 𝒮) (z 𝒮)).app X) :=
  (mono_iff_injective _).1 inferInstance

/-- Equal natural transformations between `Type`-valued functors agree on elements. -/
private theorem app_apply_congr {C : Type*} [Category C] {F G : C ⥤ Type (u + 1)}
    {f g : F ⟶ G}
    (h : f = g) (X : C) (x : F.obj X) : f.app X x = g.app X x := by
  rw [h]

include hT hmono in
/-- **The intersection of the equalizers is an algebraic space affine over `T`.**  Let
`φ : R ⟶ L` be injective at every test scheme with image the elements equalized by every pair
`α_𝒮, z_𝒮`.  If `L` and every `Q_𝒮` are algebraic spaces affine over `T`, so is `R`. -/
theorem isAffineAlgebraicSpaceOver_of_injective_of_forall_eq (hZ : B.Contains (⊤_ Scheme.{u}))
    (hL : IsAffineAlgebraicSpaceOver ((schemeSpaceFunctor B S hS).obj T) L)
    (hQ : ∀ 𝒮, IsAffineAlgebraicSpaceOver ((schemeSpaceFunctor B S hS).obj T) (Q 𝒮))
    (φ : R ⟶ L) (hφ : ∀ X, Function.Injective (φ.app X))
    (himage : ∀ X (y : L.obj X), (∀ 𝒮, (α 𝒮).app X y = (z 𝒮).app X y) → ∃ x, φ.app X x = y)
    (hφeq : ∀ 𝒮, φ ≫ α 𝒮 = φ ≫ z 𝒮) :
    IsAffineAlgebraicSpaceOver ((schemeSpaceFunctor B S hS).obj T) R := by
  have hD : ∀ 𝒮, IsAffineAlgebraicSpaceOver ((schemeSpaceFunctor B S hS).obj T)
      ((equalizerSystem B S hS Q α z hmono).obj 𝒮) :=
    fun 𝒮 => isAffineAlgebraicSpaceOver_of_isLimit_fork B S hS hL (hQ 𝒮.unop)
      (Fork.ofι _ (equalizer.condition (α 𝒮.unop) (z 𝒮.unop))) (equalizerIsEqualizer _ _)
  have hinj : ∀ {𝒮 𝒮' : (Finset ι)ᵒᵖ} (f : 𝒮 ⟶ 𝒮') (X : (SchemesOver
      ((schemeSpaceFunctor B S hS).obj T))ᵒᵖ),
      Function.Injective (((equalizerSystem B S hS Q α z hmono).map f).app X) := by
    intro 𝒮 𝒮' f X a b hab
    have h := app_apply_congr (equalizerSystem_map_ι B S hS Q α z hmono f) X
    apply injective_equalizer_ι_app B S hS Q α z 𝒮.unop X
    exact (h a).symm.trans ((congrArg _ hab).trans (h b))
  -- the cone with vertex `R`
  let c : Cone (equalizerSystem B S hS Q α z hmono) :=
    { pt := R
      π :=
        { app := fun 𝒮 => equalizer.lift φ (hφeq 𝒮.unop)
          naturality := fun 𝒮 𝒮' f => equalizer.hom_ext
            ((congrArg (· ≫ equalizer.ι (α 𝒮'.unop) (z 𝒮'.unop)) (Category.id_comp _)).trans
              ((equalizer.lift_ι _ _).trans ((equalizer.lift_ι φ (hφeq 𝒮.unop)).symm.trans
                ((congrArg (equalizer.lift φ (hφeq 𝒮.unop) ≫ ·)
                  (equalizerSystem_map_ι B S hS Q α z hmono f).symm).trans
                  (Category.assoc _ _ _).symm)))) } }
  have hc : IsLimit c := by
    refine evaluationJointlyReflectsLimits _ fun X => Nonempty.some
      ((Types.isLimit_iff _).mpr ?_)
    intro s hs
    let ιX : ∀ 𝒮 : (Finset ι)ᵒᵖ, ((equalizerSystem B S hS Q α z hmono).obj 𝒮).obj X → L.obj X :=
      fun 𝒮 => (equalizer.ι (α 𝒮.unop) (z 𝒮.unop)).app X
    have hιX : ∀ {𝒮 𝒮' : (Finset ι)ᵒᵖ} (f : 𝒮 ⟶ 𝒮')
        (a : ((equalizerSystem B S hS Q α z hmono).obj 𝒮).obj X),
        ιX 𝒮' (((equalizerSystem B S hS Q α z hmono).map f).app X a) = ιX 𝒮 a := fun f a =>
      app_apply_congr (equalizerSystem_map_ι B S hS Q α z hmono f) X a
    have hιXinj : ∀ 𝒮, Function.Injective (ιX 𝒮) := fun 𝒮 =>
      injective_equalizer_ι_app B S hS Q α z 𝒮.unop X
    have hιXeq : ∀ 𝒮 (a : ((equalizerSystem B S hS Q α z hmono).obj 𝒮).obj X),
        (α 𝒮.unop).app X (ιX 𝒮 a) = (z 𝒮.unop).app X (ιX 𝒮 a) := fun 𝒮 a =>
      app_apply_congr (equalizer.condition (α 𝒮.unop) (z 𝒮.unop)) X a
    have hconst : ∀ 𝒮 : (Finset ι)ᵒᵖ, ιX 𝒮 (s 𝒮) = ιX (op ∅) (s (op ∅)) := fun 𝒮 =>
      ((congrArg (ιX (op ∅)) (hs (homOfLE (Finset.empty_subset 𝒮.unop)).op)).symm.trans
        (hιX _ _)).symm
    obtain ⟨x, hx⟩ := himage X (ιX (op ∅) (s (op ∅))) fun 𝒮 => by
      rw [← hconst (op 𝒮)]
      exact hιXeq (op 𝒮) (s (op 𝒮))
    have hπι : ∀ 𝒮 (x' : R.obj X), ιX 𝒮 ((c.π.app 𝒮).app X x') = φ.app X x' := fun 𝒮 x' =>
      app_apply_congr (equalizer.lift_ι φ (hφeq 𝒮.unop)) X x'
    refine ⟨x, fun 𝒮 => hιXinj 𝒮 ((hπι 𝒮 x).trans (hx.trans (hconst 𝒮).symm)), fun x' hx' => ?_⟩
    apply hφ X
    rw [hx, ← hπι (op ∅) x']
    exact congrArg (ιX (op ∅)) (hx' (op ∅))
  exact isAffineAlgebraicSpaceOver_of_isLimit_of_siteContainsBaseChangeLimits B S hS hT _ hD hZ
    (siteContainsBaseChangeLimits_predicateSystem_of_injective B S hS _ hD
      fun f X => hinj f X) c hc

end Intersection

end AlgebraicGeometry.Space

end
