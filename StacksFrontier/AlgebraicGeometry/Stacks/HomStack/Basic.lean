module

public import StacksFrontier.CategoryTheory.FiberedInGroupoids.BasePullback
public import StacksFrontier.Deformation.Artin.FormalObject.NonEffectiveOfClasses
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts

/-!
# The Hom-stack out of an object of the big fppf site

Let `S` be a scheme, let `X` be a scheme over `S` and let `𝒵` be a category fibred in groupoids
over `(Sch/S)_fppf`. The *Hom-stack* `Mor_S(X, 𝒵)` of Section 0AF8 of the source has as fibre
over an `S`-scheme `T` the groupoid `Mor_T(X ×_S T, 𝒵 ×_S T)` of 1-morphisms and 2-morphisms.
By the 2-Yoneda lemma (Stacks 004B) a 1-morphism `X ×_S T ⟶ 𝒵 ×_S T` over `T` is the same as a
1-morphism `X ×_S T ⟶ 𝒵` over `S`, which is an object of `𝒵` over `X ×_S T`; this is the
identification `Mor_T(X ×_S T, 𝒵 ×_S T) = Mor_S(X ×_S T, 𝒵)` displayed in the source. So
`Mor_S(X, 𝒵)` is the pullback of `𝒵` along the base change functor `T ↦ X ×_S T` of the big
fppf site: an object over `T` is an object of `𝒵` over `X ×_S T`, and a morphism over
`g : T' ⟶ T` is a morphism of `𝒵` over `X ×_S g`. That is the definition used here.

## Main definitions

* `AlgebraicGeometry.Stack.homStack X 𝒵`: the Hom-stack `Mor_S(X, 𝒵)`, a based category over the
  big fppf site of `S`, with the universes of the 2-category of algebraic stacks when `𝒵` has
  them.
* `AlgebraicGeometry.Stack.homStackClass`: a classifying invariant of `𝒵` with values in a
  presheaf `P` induces one of `Mor_S(X, 𝒵)` with values in `T ↦ P(X ×_S T)`.

## Main results

* `AlgebraicGeometry.Stack.isFiberedInGroupoids_homStack`: `Mor_S(X, 𝒵)` is fibred in groupoids
  when `𝒵` is.
* `AlgebraicGeometry.Stack.isClassifyingInvariant_homStackClass`.
-/

@[expose] public noncomputable section

namespace AlgebraicGeometry.Stack

open CategoryTheory CategoryTheory.Limits Opposite BasedCategory Functor Deformation.Artin

universe u v t w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The base change functor `T ↦ X ×_S T` of the big fppf site of `S`. -/
abbrev baseChangeFunctor (X : BigFppfOver B S hS) : BigFppfOver B S hS ⥤ BigFppfOver B S hS :=
  prod.functor.obj X

/-- **The Hom-stack `Mor_S(X, 𝒵)`** (Section 0AF8). For an object `X` of the big fppf site of `S`
and a category `𝒵` over it, the category over the big fppf site of `S` whose objects over `T` are
the objects of `𝒵` over `X ×_S T` and whose morphisms over `g : T' ⟶ T` are the morphisms of `𝒵`
over `X ×_S g`: by the 2-Yoneda lemma, the groupoid of 1-morphisms `X ×_S T ⟶ 𝒵` over `S`, which
is the source's `Mor_T(X ×_S T, 𝒵 ×_S T)`. -/
abbrev homStack (X : BigFppfOver B S hS) (𝒵 : BasedCategory.{v, t} (BigFppfOver B S hS)) :
    BasedCategory.{max u v, max (u + 1) t} (BigFppfOver B S hS) :=
  basePullback (baseChangeFunctor X) 𝒵

variable (X : BigFppfOver B S hS) (𝒵 : BasedCategory.{v, t} (BigFppfOver B S hS))

/-- **`Mor_S(X, 𝒵)` is fibred in groupoids** when `𝒵` is. -/
theorem isFiberedInGroupoids_homStack (h𝒵 : 𝒵.p.IsFiberedInGroupoids) :
    (homStack X 𝒵).p.IsFiberedInGroupoids :=
  isFiberedInGroupoids_basePullback _ 𝒵 h𝒵

/-! ### Classifying invariants of the Hom-stack -/

variable {X 𝒵}

/-- The invariant of an object of `F^* 𝒵` induced by an invariant of `𝒵`: the invariant of the
underlying object of `𝒵`, read on `F T`. -/
def basePullbackClass (F : BigFppfOver B S hS ⥤ BigFppfOver B S hS)
    {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type w} (cl : ∀ z : 𝒵.obj, P.obj (op (𝒵.p.obj z)))
    (x : BasePullbackObj F 𝒵) : (F.op ⋙ P).obj (op x.base) :=
  P.map (eqToHom x.over.symm).op (cl x.obj)

/-- A classifying invariant of a category fibred in groupoids `𝒵` with values in `P` induces a
classifying invariant of `F^* 𝒵` with values in `F^* P`. -/
theorem isClassifyingInvariant_basePullbackClass (F : BigFppfOver B S hS ⥤ BigFppfOver B S hS)
    (h𝒵 : 𝒵.p.IsFiberedInGroupoids)
    {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type w} {cl : ∀ z : 𝒵.obj, P.obj (op (𝒵.p.obj z))}
    (hcl : IsClassifyingInvariant P cl) :
    IsClassifyingInvariant (p := (basePullback F 𝒵).p) (F.op ⋙ P)
      (basePullbackClass F cl) where
  naturality := by
    intro (x' : BasePullbackObj F 𝒵) (x : BasePullbackObj F 𝒵) φ
    change P.map _ (cl x'.obj) = P.map (F.map (BasePullbackObj.Hom.base φ)).op
      (P.map _ (cl x.obj))
    rw [hcl.naturality (BasePullbackObj.Hom.hom φ),
      IsHomLift.fac' 𝒵.p (F.map (BasePullbackObj.Hom.base φ)) (BasePullbackObj.Hom.hom φ)]
    simp only [← Functor.map_comp_apply, ← op_comp, eqToHom_trans_assoc,
      eqToHom_refl, Category.id_comp]
  surjective := by
    intro U c
    obtain ⟨z, hz, hzc⟩ := hcl.surjective_strict h𝒵 (F.obj U) c
    refine ⟨(⟨U, z, hz⟩ : BasePullbackObj F 𝒵), Iso.refl _, ?_⟩
    change P.map (eqToHom hz.symm).op (cl z) = P.map (F.map (𝟙 U)).op c
    rw [hzc, F.map_id]
    simp only [← Functor.map_comp_apply, ← op_comp, eqToHom_trans, eqToHom_refl, op_id,
      Functor.map_id_apply]
  injective := by
    intro (x₁ : BasePullbackObj F 𝒵) (x₂ : BasePullbackObj F 𝒵) (e : x₁.base ≅ x₂.base) he
    change P.map _ (cl x₁.obj) = P.map (F.map e.hom).op (P.map _ (cl x₂.obj)) at he
    let e' : 𝒵.p.obj x₁.obj ≅ 𝒵.p.obj x₂.obj :=
      eqToIso x₁.over ≪≫ F.mapIso e ≪≫ eqToIso x₂.over.symm
    obtain ⟨φ, hφ⟩ := hcl.injective x₁.obj x₂.obj e' (by
      change cl x₁.obj = P.map (eqToHom x₁.over ≫ F.map e.hom ≫ eqToHom x₂.over.symm).op
        (cl x₂.obj)
      rw [op_comp, op_comp, Functor.map_comp_apply, Functor.map_comp_apply, ← he,
        ← Functor.map_comp_apply, ← op_comp, eqToHom_trans, eqToHom_refl, op_id,
        Functor.map_id_apply])
    have hl : 𝒵.p.IsHomLift (F.map e.hom) φ :=
      IsHomLift.of_fac' 𝒵.p _ _ x₁.over x₂.over (by rw [hφ]; rfl)
    exact ⟨(⟨e.hom, φ, hl⟩ : BasePullbackObj.Hom x₁ x₂), rfl⟩

/-- The invariant of an object of `Mor_S(X, 𝒵)` induced by an invariant of `𝒵`. -/
abbrev homStackClass {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type w}
    (cl : ∀ z : 𝒵.obj, P.obj (op (𝒵.p.obj z))) (x : (homStack X 𝒵).obj) :
    ((baseChangeFunctor X).op ⋙ P).obj (op ((homStack X 𝒵).p.obj x)) :=
  basePullbackClass (baseChangeFunctor X) cl x

/-- A classifying invariant of `𝒵` with values in `P` induces a classifying invariant of
`Mor_S(X, 𝒵)` with values in `T ↦ P(X ×_S T)`. -/
theorem isClassifyingInvariant_homStackClass (h𝒵 : 𝒵.p.IsFiberedInGroupoids)
    {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type w} {cl : ∀ z : 𝒵.obj, P.obj (op (𝒵.p.obj z))}
    (hcl : IsClassifyingInvariant P cl) :
    IsClassifyingInvariant (p := (homStack X 𝒵).p) ((baseChangeFunctor X).op ⋙ P)
      (homStackClass (X := X) cl) :=
  isClassifyingInvariant_basePullbackClass _ h𝒵 hcl

end AlgebraicGeometry.Stack
